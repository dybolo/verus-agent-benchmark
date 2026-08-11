use std::path::PathBuf;
use std::fs;
use proc_macro2::{Delimiter, TokenStream, TokenTree};
use quote::ToTokens;
use crate::{utils::*, DeghostMode};
use crate::deghost::{normalize_atomic_with_ghost_block, remove_ghost_block, remove_verus_macro, remove_ghost_sig};
use syn_verus::FnMode::*;

/*
Checks whether attribute contains instructions about completing a proof
*/
fn is_proof_attr(attr: &syn_verus::Attribute) -> bool {
    attr.path().segments.len() > 1
    && attr.path().segments[0].ident.to_string() == "verifier"
    && (attr.path().segments[1].ident.to_string() == "rlimit"
        || attr.path().segments[1].ident.to_string() == "integer_ring"
        || attr.path().segments[1].ident.to_string() == "memoize"
        || attr.path().segments[1].ident.to_string() == "loop_isolation"
        || attr.path().segments[1].ident.to_string() == "spinoff_prover")
}

pub fn remove_proof_attr(attr: &Vec<syn_verus::Attribute>) -> Vec<syn_verus::Attribute> {
    attr.iter().filter(|a| !is_proof_attr(a)).map(|a| a.clone()).collect()
}

/// State-machine transition inductive functions are proof functions in Verus,
/// even though their source syntax omits the `proof` keyword.
fn is_inductive_fn(attrs: &[syn_verus::Attribute]) -> bool {
    attrs.iter().any(|attr| attr.path().is_ident("inductive"))
}

fn is_inductive_attribute(tokens: &[TokenTree], index: usize) -> bool {
    matches!(tokens.get(index), Some(TokenTree::Punct(p)) if p.as_char() == '#')
        && matches!(tokens.get(index + 1), Some(TokenTree::Group(group))
            if group.delimiter() == Delimiter::Bracket
                && matches!(group.stream().into_iter().next(), Some(TokenTree::Ident(ident)) if ident == "inductive"))
}

fn inductive_body_index(tokens: &[TokenTree], attribute: usize) -> Option<usize> {
    if !is_inductive_attribute(tokens, attribute)
        || !matches!(tokens.get(attribute + 2), Some(TokenTree::Ident(ident)) if ident == "fn")
    {
        return None;
    }

    ((attribute + 3)..tokens.len()).find(|index| {
        matches!(tokens.get(*index), Some(TokenTree::Group(group)) if group.delimiter() == Delimiter::Brace)
    })
}

fn token_slices_are_equal(original: &[TokenTree], changed: &[TokenTree]) -> bool {
    original.len() == changed.len()
        && original.iter().zip(changed.iter()).all(|(original, changed)| {
            original.to_string() == changed.to_string()
        })
}

/// Compare state-machine macro tokens while allowing completion of only an
/// originally empty `#[inductive(...)] fn` body. All declaration tokens and
/// every non-target transition remain exact matches.
fn state_machine_tokens_are_safe(original: TokenStream, changed: TokenStream) -> bool {
    let original: Vec<TokenTree> = original.into_iter().collect();
    let changed: Vec<TokenTree> = changed.into_iter().collect();
    let mut original_index = 0;
    let mut changed_index = 0;

    while original_index < original.len() && changed_index < changed.len() {
        if is_inductive_attribute(&original, original_index)
            && is_inductive_attribute(&changed, changed_index)
        {
            if let (Some(original_body), Some(changed_body)) = (
                inductive_body_index(&original, original_index),
                inductive_body_index(&changed, changed_index),
            ) {
                if !token_slices_are_equal(
                    &original[original_index..original_body],
                    &changed[changed_index..changed_body],
                ) {
                    return false;
                }
                match (&original[original_body], &changed[changed_body]) {
                    (TokenTree::Group(original_group), TokenTree::Group(changed_group))
                        if original_group.delimiter() == Delimiter::Brace
                            && changed_group.delimiter() == Delimiter::Brace
                            && original_group.stream().is_empty() =>
                    {
                        original_index = original_body + 1;
                        changed_index = changed_body + 1;
                        continue;
                    }
                    _ => {}
                }
            }
        }

        match (&original[original_index], &changed[changed_index]) {
            (TokenTree::Group(original_group), TokenTree::Group(changed_group))
                if original_group.delimiter() == changed_group.delimiter() =>
            {
                if !state_machine_tokens_are_safe(original_group.stream(), changed_group.stream()) {
                    return false;
                }
            }
            (original_tree, changed_tree) if original_tree.to_string() == changed_tree.to_string() => {}
            _ => return false,
        }
        original_index += 1;
        changed_index += 1;
    }

    original_index == original.len() && changed_index == changed.len()
}

fn tokenized_state_machine_change_is_safe(
    original: &syn_verus::ItemMacro,
    changed: &syn_verus::ItemMacro,
) -> bool {
    original.attrs == changed.attrs
        && original.ident == changed.ident
        && original.semi_token == changed.semi_token
        && original.mac.path.is_ident("tokenized_state_machine")
        && changed.mac.path.is_ident("tokenized_state_machine")
        && original.mac.delimiter == changed.mac.delimiter
        && state_machine_tokens_are_safe(original.mac.tokens.clone(), changed.mac.tokens.clone())
}

/*
Erases all ghost code from exec fn only. Leaves all other fn types unchanged.
*/
fn remove_ghost_from_exec_fn(func: &syn_verus::ItemFn) -> syn_verus::ItemFn {
    match func.sig.mode {
        Exec(_) | Default => {
            match remove_ghost_block(&(*func.block), &DeghostMode::default()) {
                Some(new_block) => {
                    syn_verus::ItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: Box::new(new_block), // Box the new block
                        semi_token: func.semi_token.clone(),
                    }
                },
                None => {
                    syn_verus::ItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: Box::new(syn_verus::Block { brace_token: func.block.brace_token.clone(), stmts: Vec::new() }), // empty block
                        semi_token: func.semi_token.clone(),
                    }
                }
            }
        },
        Spec(_) | SpecChecked(_) | Proof(_) | ProofAxiom(_) => {
            func.clone()
        },
    }
}

fn remove_ghost_from_impl_exec_fn(func: &syn_verus::ImplItemFn) -> syn_verus::ImplItemFn {
    match func.sig.mode {
        Exec(_) | Default => {
            match remove_ghost_block(&func.block, &DeghostMode::default()) {
                Some(new_block) => {
                    syn_verus::ImplItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        defaultness: func.defaultness.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: new_block,
                        semi_token: func.semi_token.clone(),
                    }
                },
                None => {
                    syn_verus::ImplItemFn {
                        attrs: remove_proof_attr(&func.attrs),
                        vis: func.vis.clone(),
                        defaultness: func.defaultness.clone(),
                        sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                        block: syn_verus::Block { brace_token: func.block.brace_token.clone(), stmts: Vec::new() }, // empty block
                        semi_token: func.semi_token.clone(),
                    }
                }
            }
        },
        Spec(_) | SpecChecked(_) | Proof(_) | ProofAxiom(_) => {
            func.clone()
        },
    }
}

fn remove_ghost_from_trait_exec_fn(func: &syn_verus::TraitItemFn) -> syn_verus::TraitItemFn {
    match func.sig.mode {
        Exec(_) | Default => {
            if func.default.is_some() {
                match remove_ghost_block(&(func.default.clone().unwrap()), &DeghostMode::default()) {
                    Some(new_block) => {
                        syn_verus::TraitItemFn {
                            attrs: remove_proof_attr(&func.attrs),
                            sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                            default: Some(new_block),
                            semi_token: func.semi_token.clone(),
                        }
                    },
                    None => {
                        syn_verus::TraitItemFn {
                            attrs: remove_proof_attr(&func.attrs),
                            sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                            default: None, // empty block
                            semi_token: func.semi_token.clone(),
                        }
                    }
                }
            } else {
                syn_verus::TraitItemFn {
                    attrs: remove_proof_attr(&func.attrs),
                    sig: remove_ghost_sig(&func.sig, &DeghostMode::default()).expect("exec fn has non-ghost sig"),
                    default: None, // empty block
                    semi_token: func.semi_token.clone(),
                }
            }
        },
        Spec(_) | SpecChecked(_) | Proof(_) | ProofAxiom(_) => {
            func.clone()
        },
    }
}

fn check_fn_signature(original: &syn_verus::Signature, changed: &syn_verus::Signature) -> bool {
    let mut orig_spec = original.spec.clone();
    orig_spec.prover = None;
    orig_spec.decreases = None;
    orig_spec.invariants = None;
    let mut changed_spec = changed.spec.clone();
    changed_spec.prover = None;
    changed_spec.decreases = None;
    changed_spec.invariants = None;
    remove_ghost_sig(original, &DeghostMode::default()) == remove_ghost_sig(changed, &DeghostMode::default())
    && orig_spec == changed_spec
}

fn check_impl_items(original_items: &[syn_verus::ImplItem], changed_items: &[syn_verus::ImplItem]) -> bool {
    let mut idx_orig = 0;
    let mut idx_changed = 0;
    while idx_orig < original_items.len() && idx_changed < changed_items.len() {
        let original = &original_items[idx_orig];
        let changed = &changed_items[idx_changed];
        match (original, changed) {
            (syn_verus::ImplItem::Fn(f_orig), syn_verus::ImplItem::Fn(f_changed)) => {
                let mysig = f_orig.sig.to_token_stream().to_string();
                let mut myfun = mysig.clone();
                if let Some(myindex) = mysig.find(')') {
                    myfun = (&mysig[..=myindex]).to_string(); // include the ')' character
                }

                if is_proof_or_exec(&f_orig.sig) && fn_body_is_target(&f_orig.block) && f_orig.sig.ident == f_changed.sig.ident {
                    // target function: deghost from exec, check signature for proof
                    if is_inductive_fn(&f_orig.attrs) {
                        if f_orig.vis != f_changed.vis
                            || remove_proof_attr(&f_orig.attrs) != remove_proof_attr(&f_changed.attrs)
                            || !check_fn_signature(&f_orig.sig, &f_changed.sig)
                        {
                            println!("Disallowed changes in inductive proof function: {}", myfun);
                            return false;
                        }
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    } else { match f_changed.sig.mode {
                        Proof(_) => {
                            if f_orig.vis != f_changed.vis {
                                println!("Disallowed changes in the visibility of proof function: {}", myfun);
                                println!(" Original visibility: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed visibility: {}\n", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else if remove_proof_attr(&f_orig.attrs) != remove_proof_attr(&f_changed.attrs) {
                                println!("Disallowed changes in the attributes of proof function: {}", myfun);
                                println!(" Original attributes: {:?}", f_orig.attrs);
                                println!(" Changed attributes: {:?}\n", f_changed.attrs);

                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {

                                println!("Disallowed changes in the signature (e.g., requires, ensures) of a proof function:");
                                println!(" Original signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed  signature: {}\n", f_changed.sig.to_token_stream().to_string());

                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        Exec(_) | Default => {
                            let deghosted_orig = remove_ghost_from_impl_exec_fn(&f_orig);
                            let deghosted_changed = remove_ghost_from_impl_exec_fn(&f_changed);
                            // after deghost, check exact match.
                            // deghost removes spec from signature. also need to check that requires/ensures/recommends do not change
                            if deghosted_orig != deghosted_changed {
                                println!("Unsafe change detected in the body of executable function: {}", myfun);
                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {
                                println!("Disallowed changes made to the signature of executable function: {}", myfun);
                                println!(" Original signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed  signature: {}\n", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        _ => {
                            return false;
                        }
                    }}
                } else {
                    // non target function: exact match
                    if f_orig != f_changed {
                        if matches!(f_orig.sig.mode, Exec(_) | Default)
                            && matches!(f_changed.sig.mode, Exec(_) | Default)
                            && f_orig.sig.ident == f_changed.sig.ident
                        {
                            let mut normalized_orig = f_orig.clone();
                            normalized_orig.block = normalize_atomic_with_ghost_block(&f_orig.block);
                            let mut normalized_changed = f_changed.clone();
                            normalized_changed.block = normalize_atomic_with_ghost_block(&f_changed.block);
                            if normalized_orig == normalized_changed {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                                continue;
                            }
                        }
                        // if the changed item is a proof fn (but not axiom) or spec fn, skip this item, we will allow it to be added
                        match f_changed.sig.mode {
                            Spec(_) | SpecChecked(_) | Proof(_) => {
                                idx_changed = idx_changed + 1;
                            },
                            _ => {
                                println!("Disallowed addition to the program: {}\n", f_changed.sig.to_token_stream().to_string());
                                return false;
                            }
                        }
                    } else {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    }
                }
            },
            (_, syn_verus::ImplItem::Macro(_)) => {
                // check exact match
                if original != changed {
                    // these items are allowed to be added. skip this item in changed file
                    idx_changed = idx_changed + 1;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (_, _) => {
                // all other items must have exact match
                if original != changed {
                    return false;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            }
        }
    }
    return idx_orig == original_items.len();
}

fn check_trait_items(original_items: &[syn_verus::TraitItem], changed_items: &[syn_verus::TraitItem]) -> bool {
    let mut idx_orig = 0;
    let mut idx_changed = 0;

    while idx_orig < original_items.len() && idx_changed < changed_items.len() {
        let original = &original_items[idx_orig];
        let changed = &changed_items[idx_changed];
        match (original, changed) {
            (syn_verus::TraitItem::Fn(f_orig), syn_verus::TraitItem::Fn(f_changed)) => {

                // Get the string name of f_orig
                let mysig = f_orig.sig.to_token_stream().to_string();
                let mut myfun = mysig.clone();
                if let Some(myindex) = mysig.find(')') {
                    myfun = (&mysig[..=myindex]).to_string(); // include the ')' character
                }

                if is_proof_or_exec(&f_orig.sig) && f_orig.default.is_some() && fn_body_is_target(&f_orig.default.clone().unwrap())
                    && f_orig.sig.ident == f_changed.sig.ident {
                    // target function: deghost from exec, check signature for proof
                    if is_inductive_fn(&f_orig.attrs) {
                        if remove_proof_attr(&f_orig.attrs) != remove_proof_attr(&f_changed.attrs)
                            || !check_fn_signature(&f_orig.sig, &f_changed.sig)
                        {
                            println!("Disallowed changes in inductive trait proof function: {}", myfun);
                            return false;
                        }
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    } else { match f_changed.sig.mode {
                        Proof(_) => {
                            if !(remove_proof_attr(&f_orig.attrs) == remove_proof_attr(&f_changed.attrs) && check_fn_signature(&f_orig.sig, &f_changed.sig)) {
                                println!("Disallowed changes detected for a trait-proof function: {}", myfun);
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        Exec(_) | Default => {
                            let deghosted_orig = remove_ghost_from_trait_exec_fn(&f_orig);
                            let deghosted_changed = remove_ghost_from_trait_exec_fn(&f_changed);
                            // after deghost, check exact match.
                            // deghost removes spec from signature. also need to check that requires/ensures/recommends do not change
                            if !(deghosted_orig == deghosted_changed && check_fn_signature(&f_orig.sig, &f_changed.sig)) {
                                println!("Disallowed changes detected for a trait-executable function: {}", myfun);
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        _ => {
                            return false;
                        }
                    }}
                } else {
                    // non target function: exact match
                    if f_orig != f_changed {
                        if matches!(f_orig.sig.mode, Exec(_) | Default)
                            && matches!(f_changed.sig.mode, Exec(_) | Default)
                            && f_orig.sig.ident == f_changed.sig.ident
                        {
                            if let (Some(orig_block), Some(changed_block)) = (&f_orig.default, &f_changed.default) {
                                let mut normalized_orig = f_orig.clone();
                                normalized_orig.default = Some(normalize_atomic_with_ghost_block(orig_block));
                                let mut normalized_changed = f_changed.clone();
                                normalized_changed.default = Some(normalize_atomic_with_ghost_block(changed_block));
                                if normalized_orig == normalized_changed {
                                    idx_orig = idx_orig + 1;
                                    idx_changed = idx_changed + 1;
                                    continue;
                                }
                            }
                        }
                        // if the changed item is a proof fn (but not axiom) or spec fn, skip this item, we will allow it to be added
                        match f_changed.sig.mode {
                            Spec(_) | SpecChecked(_) | Proof(_) => {
                                idx_changed = idx_changed + 1;
                            },
                            _ => {
                                return false;
                            }
                        }
                    } else {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    }
                }
            },
            (_, syn_verus::TraitItem::Macro(_)) => {
                // check exact match
                if original != changed {
                    // these items are allowed to be added. skip this item in changed file
                    idx_changed = idx_changed + 1;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (_, _) => {
                // all other items must have exact match
                if original != changed {
                    return false;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            }
        }
    }
    return idx_orig == original_items.len();
}

fn mod_decl_is_equal(original: &syn_verus::ItemMod, changed: &syn_verus::ItemMod) -> bool {
    original.attrs == changed.attrs &&
    original.vis == changed.vis &&
    original.unsafety == changed.unsafety &&
    original.mod_token == changed.mod_token &&
    original.ident == changed.ident &&
    original.semi == changed.semi
}

fn check_items(original_items: &[syn_verus::Item], changed_items: &[syn_verus::Item]) -> bool
{
    let mut idx_orig = 0;
    let mut idx_changed = 0;

    while idx_orig < original_items.len() && idx_changed < changed_items.len() {
        let original = &original_items[idx_orig];
        let changed = &changed_items[idx_changed];
        match (original, changed) {
            (syn_verus::Item::Fn(f_orig), syn_verus::Item::Fn(f_changed)) => {

                // Get the string name of f_orig
                let mysig = f_orig.sig.to_token_stream().to_string();
                let mut myfun = mysig.clone();
                if let Some(myindex) = mysig.find(')') {
                    myfun = (&mysig[..=myindex]).to_string(); // include the ')' character
                }

                let mynewsig = f_changed.sig.to_token_stream().to_string();
                let mut mynewfun = mynewsig.clone();
                if let Some(mynewindex) = mynewsig.find(')') {
                   mynewfun = (&mynewsig[..=mynewindex]).to_string(); // include the ')' character
                }

                if is_proof_or_exec(&f_orig.sig) && fn_body_is_target(&*f_orig.block) && f_orig.sig.ident == f_changed.sig.ident {
                    // target function: deghost from exec, check signature for proof
                    if is_inductive_fn(&f_orig.attrs) {
                        if f_orig.vis != f_changed.vis
                            || remove_proof_attr(&f_orig.attrs) != remove_proof_attr(&f_changed.attrs)
                            || !check_fn_signature(&f_orig.sig, &f_changed.sig)
                        {
                            println!("Disallowed changes in inductive proof function: {}", myfun);
                            return false;
                        }
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    } else { match f_changed.sig.mode {
                        Proof(_) => {
                            if f_orig.vis != f_changed.vis {
                                println!("Disallowed changes in the visibility of proof function: {}", myfun);
                                println!(" Original visibility: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed visibility: {}", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else if remove_proof_attr(&f_orig.attrs) != remove_proof_attr(&f_changed.attrs) {
                                println!("Disallowed changes in the attributes of proof function: {}", myfun);
                                println!(" Original attributes: {:?}", f_orig.attrs);
                                println!(" Changed attributes: {:?}", f_changed.attrs);

                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {

                                println!("Disallowed changes found in the signature (e.g., requires, ensures) of a proof function:");
                                println!(" Original signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!(" Changed  signature: {}", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        Exec(_) | Default => {
                            let deghosted_orig = remove_ghost_from_exec_fn(&f_orig);
                            let deghosted_changed = remove_ghost_from_exec_fn(&f_changed);
                            // after deghost, check exact match.
                            // deghost removes spec from signature. also need to check that requires/ensures/recommends do not change
                            if deghosted_orig != deghosted_changed {
                                // Print out error information
                                println!("Disallowed changes found in the body of function: {}", myfun);

                                return false;
                            } else if !check_fn_signature(&f_orig.sig, &f_changed.sig) {

                                // Print out error information
                                println!("Disallowed changes found in an executable function's requires/ensures conditions");
                                println!("\tOriginal signature: {}", f_orig.sig.to_token_stream().to_string());
                                println!("\tChanged  signature: {}", f_changed.sig.to_token_stream().to_string());
                                return false;
                            } else {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                            }
                        },
                        _ => {
                            return false;
                        }
                    }}
                } else {
                    // non target function: exact match
                    if f_orig != f_changed {
                        if matches!(f_orig.sig.mode, Exec(_) | Default)
                            && matches!(f_changed.sig.mode, Exec(_) | Default)
                            && f_orig.sig.ident == f_changed.sig.ident
                        {
                            let mut normalized_orig = f_orig.clone();
                            normalized_orig.block = Box::new(normalize_atomic_with_ghost_block(&f_orig.block));
                            let mut normalized_changed = f_changed.clone();
                            normalized_changed.block = Box::new(normalize_atomic_with_ghost_block(&f_changed.block));
                            if normalized_orig == normalized_changed {
                                idx_orig = idx_orig + 1;
                                idx_changed = idx_changed + 1;
                                continue;
                            }
                        }
                        // if the changed item is a proof fn (but not axiom) or spec fn, skip this item, we will allow it to be added
                        match f_changed.sig.mode {
                            Spec(_) | SpecChecked(_) | Proof(_) => {
                                idx_changed = idx_changed + 1;
                            },
                            _ => {
                                println!("Disallowed addition of a new function: {}", mynewfun);
                                return false;
                            }
                        }
                    } else {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    }
                }
            },
            (syn_verus::Item::Impl(i_orig), syn_verus::Item::Impl(i_changed)) => {
                // exact match for everything besides verifier attrs
                let mut orig_clone = i_orig.clone();
                orig_clone.items = Vec::new();
                orig_clone.attrs = remove_proof_attr(&orig_clone.attrs);
                let mut changed_clone = i_changed.clone();
                changed_clone.items = Vec::new();
                changed_clone.attrs = remove_proof_attr(&changed_clone.attrs);
                // check exact match, then check child items
                if orig_clone != changed_clone {
                    return false;
                } else if !check_impl_items(&i_orig.items[0..], &i_changed.items[0..]) {
                    println!("Disallowed changes made to impl block: {}", i_orig.self_ty.to_token_stream().to_string());
                    // println!("{:#?}", i_orig);
                    // println!("{:#?}", i_changed);
                    return false;
                }
                else {
                    // then advance to next item
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (syn_verus::Item::Trait(t_orig), syn_verus::Item::Trait(t_changed)) => {
                // exact match for everything besides verifier attrs
                let mut orig_clone = t_orig.clone();
                orig_clone.items = Vec::new();
                orig_clone.attrs = remove_proof_attr(&orig_clone.attrs);
                let mut changed_clone = t_changed.clone();
                changed_clone.items = Vec::new();
                changed_clone.attrs = remove_proof_attr(&changed_clone.attrs);
                // check exact match, then check child items
                if !(orig_clone == changed_clone && check_trait_items(&t_orig.items[0..], &t_changed.items[0..])) {
                    return false;
                } else {
                    // then advance to next item
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (_, syn_verus::Item::Use(_)) | (_, syn_verus::Item::Macro(_)) | (_, syn_verus::Item::BroadcastUse(_)) => {
                // check exact match
                if original != changed {
                    if let (syn_verus::Item::Macro(original_macro), syn_verus::Item::Macro(changed_macro)) = (original, changed) {
                        if tokenized_state_machine_change_is_safe(original_macro, changed_macro) {
                            idx_orig = idx_orig + 1;
                            idx_changed = idx_changed + 1;
                            continue;
                        }
                    }
                    // these items are allowed to be added. skip this item in changed file
                    idx_changed = idx_changed + 1;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            },
            (syn_verus::Item::Mod(m_orig), syn_verus::Item::Mod(m_changed)) => {
                if !mod_decl_is_equal(&m_orig, &m_changed) {
                    println!("Disallowed changes made to module declaration: {}", m_orig.ident.to_string());
                    return false;
                }

                match (&m_orig.content, &m_changed.content) {
                    (Some((orig_br, orig_items)), Some((changed_br, changed_items))) => {
                        if orig_br != changed_br {
                            println!("Disallowed changes made to module content braces: {}", m_orig.ident.to_string());
                            return false;
                        } else if !check_items(&orig_items[0..], &changed_items[0..]) {
                            return false;
                        } else {
                            idx_orig = idx_orig + 1;
                            idx_changed = idx_changed + 1;
                        }
                    },
                    (None, None) => {
                        idx_orig = idx_orig + 1;
                        idx_changed = idx_changed + 1;
                    },
                    _ => {
                        println!("Disallowed changes made to module content: {}", m_orig.ident.to_string());
                        return false;
                    }
                }

            },
            (_, _) => {
                if original != changed {
                    println!("{:#?}", changed);
                    println!("{:#?}", original);
                    println!("{}", changed.to_token_stream().to_string());
                    println!("{}", original.to_token_stream().to_string());
                    return false;
                } else {
                    idx_orig = idx_orig + 1;
                    idx_changed = idx_changed + 1;
                }
            }
        }
    }
    return idx_orig == original_items.len();
}

/*
Safety check rules:
- we can add new spec fns or proof fns
- we cannot change existing spec, proof, or exec fns -- EXCEPT the target function
- we cannot change the signature of the target function, except to add decreases, opens invariants, or prover clause
- we cannot change exec code in the body of the target function
- functions annotated with `#[inductive(...)]` are transition proof functions;
  their target body may be completed as proof code while their declaration is preserved
- in any existing exec function, we may change only the proof body of a
  well-formed `atomic_with_ghost!(... ghost binding => { ... })` invocation;
  its target, operation, and other clauses must remain unchanged
- the target function is identified by being a proof or exec fn whose body does not contain `unimplemented!()`.
    all other proof and exec fn will have a body with `unimplemented!()`
*/
pub fn check_allowed_additions_only(original_file: PathBuf, changed_file: PathBuf) -> Result<bool, Error> {
    let original = fload_file(&original_file)?;
    let changed = fload_file(&changed_file)?;
    let original_source = fs::read_to_string(&original_file).map_err(Error::ReadFile)?;
    let changed_source = fs::read_to_string(&changed_file).map_err(Error::ReadFile)?;

    let original_pure_file = remove_verus_macro(&original);
    let changed_pure_file = remove_verus_macro(&changed);

    if !check_items(&original_pure_file.items[0..], &changed_pure_file.items[0..]) {
        return Ok(false);
    }

    extract_verus_macro_with_context(&original, &original_file, &original_source).and_then(|original_verus_macros| {
        extract_verus_macro_with_context(&changed, &changed_file, &changed_source).and_then(|changed_verus_macros| {

            if original_verus_macros.len() != changed_verus_macros.len() {
                println!("Disallowed changes made to Verus macros in the original files.");
                return Ok(false);
            }

            // original_verus_macros.iter().for_each(|m| {
            //     println!("{}", fprint_file(&m, Formatter::VerusFmt))
            // });

            // changed_verus_macros.iter().for_each(|m| {
            //     println!("{}", fprint_file(&m, Formatter::VerusFmt))
            // });

            for i in 0..original_verus_macros.len() {
                // Nested `verus!` macros are collected and checked separately.
                // Remove them from the enclosing parsed macro so their token
                // bodies are not also treated as opaque executable changes.
                let original_macro = remove_verus_macro(&original_verus_macros[i]);
                let changed_macro = remove_verus_macro(&changed_verus_macros[i]);
                if !check_items(&original_macro.items[0..], &changed_macro.items[0..]) {
                    println!("Disallowed changes made to Verus macros in the original files.");
                    return Ok(false);
                }
            }

            Ok(true)
        })
    })
}
