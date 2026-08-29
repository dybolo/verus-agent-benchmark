import { mkdtemp, writeFile } from "node:fs/promises";
import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import {
	DEFAULT_MAX_BYTES,
	DEFAULT_MAX_LINES,
	formatSize,
	type TruncationResult,
	truncateHead,
	withFileMutationQueue,
} from "@earendil-works/pi-coding-agent";
import { Text } from "@earendil-works/pi-tui";
import { execSync } from "child_process";
import { tmpdir } from "os";
import { join } from "path";
import { Type } from "typebox";

const SemanticGrepParams = Type.Object({
	query: Type.Optional(Type.String({ description: "Structured proof plan to search for. After analysing the problem, produce a plan following this template: 'What needs to be shown', 'Assumptions', 'Key ideas', 'High-level strategy', 'Sub-goals'. The tool returns code snippets relevant to this plan." })),
	numResults: Type.Optional(Type.Number({ description: "Number of results to return (default: 10)" })),
	type: Type.Optional(Type.Enum(["proofs", "specs"], { description: "Filter results by type: 'proofs' for proof code or 'specs' for specifications (default: all). Use to narrow proof plan search to the relevant category." })),
});

interface SemanticGrepDetails {
	query?: string;
	type?: string;
	resultCount: number;
	truncation?: TruncationResult;
	fullOutputPath?: string;
}

export default function (pi: ExtensionAPI) {
	pi.registerTool({
		name: "semantic_grep",
		label: "Semantic Grep",
        description: `Semantic search over Verus proofs and specifications using structured proof plans as queries.
		After analysing a verification problem, supply a proof plan following the template:
		"What needs to be shown", "Assumptions", "Key ideas", "High-level strategy", "Sub-goals".
		The tool returns code snippets relevant to that plan — proof strategies, specifications,
		and patterns that match the structure of your proof goal. Proofs and specs are automatically
		classified, semantically embedded, and indexed for similarity search across your repository.

		Example proof plan:
		What needs to be shown: The combined liveness assumptions are stable across all execution suffixes.
		Assumptions: Base invariant package is stable; desired-state condition holds forever.
		Key ideas: Stability is preserved under conjunction; build the full condition from smaller stable pieces.
		High-level strategy: Prove each phase invariant stable individually, then combine.
		Sub-goals: Show phase I stable; show phase II stable; show phase III stable; combine all phases.`,
		parameters: SemanticGrepParams,

		async execute(_toolCallId, params, _signal, _onUpdate, ctx) {
			const { query, numResults, type } = params;

			const args = [];

			if (query) {
				args.push("--search");
				args.push(`"${query.replace(/"/g, '\\"')}"`);
			}
			if (numResults !== undefined) {
				args.push("--num-results");
				args.push(numResults.toString());
			}
			if (type !== undefined) {
				args.push("--type");
				args.push(type);
			}

			let output: string;
			try {
				output = execSync(`semantic_grep ${args.join(" ")}`, {
					cwd: ctx.cwd,
					encoding: "utf-8",
					maxBuffer: 100 * 1024 * 1024,
				});
			} catch (err: any) {
				output = err.stdout ? err.stdout.toString() : "";
				const stderr = err.stderr ? err.stderr.toString() : "";
				if (!output && !stderr) {
					throw new Error(`semantic_grep failed: ${err.message}`);
				}
				output += "\n" + stderr;
			}

			if (!output.trim()) {
				return {
					content: [{ type: "text", text: "No results found" }],
					details: { query, type, resultCount: 0 } as SemanticGrepDetails,
				};
			}

			let resultCount = 0;
			try {
				const jsonOutput = JSON.parse(output);
				resultCount = jsonOutput.num_results || 0;
			} catch {
				resultCount = output.split("\n").filter((line) => line.trim()).length;
			}

			const truncation = truncateHead(output, {
				maxLines: DEFAULT_MAX_LINES,
				maxBytes: DEFAULT_MAX_BYTES,
			});

			const details: SemanticGrepDetails = {
				query,
				type,
				resultCount
			};

			let resultText = truncation.content;

			if (truncation.truncated) {
				const tempDir = await mkdtemp(join(tmpdir(), "pi-semantic_grep-"));
				const tempFile = join(tempDir, "output.txt");
				await withFileMutationQueue(tempFile, async () => {
					await writeFile(tempFile, output, "utf8");
				});

				details.truncation = truncation;
				details.fullOutputPath = tempFile;

				const truncatedLines = truncation.totalLines - truncation.outputLines;
				const truncatedBytes = truncation.totalBytes - truncation.outputBytes;

				resultText += `\n\n[Output truncated: showing ${truncation.outputLines} of ${truncation.totalLines} lines`;
				resultText += ` (${formatSize(truncation.outputBytes)} of ${formatSize(truncation.totalBytes)}).`;
				resultText += ` ${truncatedLines} lines (${formatSize(truncatedBytes)}) omitted.`;
				resultText += ` Full output saved to: ${tempFile}]`;
			}

			return {
				content: [{ type: "text", text: resultText }],
				details,
			};
		},

		// Custom rendering of the tool call (shown before/during execution)
		renderCall(args, theme, _context) {
			let text = theme.fg("toolTitle", theme.bold("semantic_grep "));
			if (args.query) {
				text += theme.fg("accent", `"${args.query}"`);
			}
			if (args.type) {
				text += theme.fg("muted", ` [${args.type}]`);
			}
			if (args.numResults) {
				text += theme.fg("dim", ` (${args.numResults} results)`);
			}
			return new Text(text, 0, 0);
		},

		// Custom rendering of the tool result
		renderResult(result, { expanded, isPartial }, theme, _context) {
			const details = result.details as SemanticGrepDetails | undefined;

			// Handle streaming/partial results
			if (isPartial) {
				return new Text(theme.fg("warning", "Searching proofs..."), 0, 0);
			}

			// No results case
			if (!details || details.resultCount === 0) {
				return new Text(theme.fg("dim", "No results found"), 0, 0);
			}

			// Build result display
			let text = theme.fg("success", `${details.resultCount} results`);

			// Show query and type context
			if (details.query) {
				text += theme.fg("muted", ` for "${details.query}"`);
			}
			if (details.type) {
				text += theme.fg("dim", ` [${details.type}]`);
			}

			// Show truncation warning if applicable
			if (details.truncation?.truncated) {
				text += theme.fg("warning", " (truncated)");
			}

			// In expanded view, show the actual results
			if (expanded) {
				const content = result.content[0];
				if (content?.type === "text") {
					// Show first 20 lines in expanded view, or all if fewer
					const lines = content.text.split("\n").slice(0, 20);
					for (const line of lines) {
						text += `\n${theme.fg("dim", line)}`;
					}
					if (content.text.split("\n").length > 20) {
						text += `\n${theme.fg("muted", "... (use read tool to see full output)")}`;
					}
				}

				// Show temp file path if truncated
				if (details.fullOutputPath) {
					text += `\n${theme.fg("dim", `Full output: ${details.fullOutputPath}`)}`;
				}
			}

			return new Text(text, 0, 0);
		},
	});
}
