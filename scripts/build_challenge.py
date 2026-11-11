#!/usr/bin/env python3
"""Assemble the auditable concrete interface; inspect its generated diff.

This helper copies definitions and theorem *types*, never theorem proofs.
Challenge imports only Mathlib/Lean. It must be compiled and semantically
reviewed independently; generation is not evidence of statement fidelity.
"""

from pathlib import Path
import json
import sys

ROOT = Path(__file__).resolve().parents[1]


def source(name):
    return (ROOT / "SparseMM" / (name + ".lean")).read_text(encoding="utf-8")


def between(text, start, end):
    return text[text.index(start):text.index(end)].rstrip() + "\n"


def theorem(text, name):
    start = text.index("theorem " + name + " ")
    stop = text.index(":= by", start)
    return text[start:stop].rstrip() + " := by\n  sorry\n"


parts = ["""module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Sqrt
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# Independent advertised statements and concrete model

Source: Gupta, Suomela, and Vahidi, *Sparse Matrix Multiplication Exponent 1.5
in the Low-bandwidth Model*, supplied 10-page PDF, SHA-256
37ff1c413e7b088bf4364e64c8886128e5fbc566e3abebb6a59c5c2a79e42672.

Theorem 4 is encoded as one public local-state distributed program, chosen
before numerical matrices, correct at its balanced output holders. Every
stage uses the concrete single-send/single-receive operational semantics below.
Messages carry one semiring value. The separate wire theorem removes public
labels and preserves any lossless encoding of values actually transmitted;
the paper's O(log n)-bit encoding premise is not manufactured from a semiring.

Integral teams use floor-sqrt(d)+1. Output balancing uses public batch
permutations; the main algorithm's routing uses 2D rounds. Exact regular-load
D-round redistribution (Lemma 3) is proved separately below. The output
assignment is an alternative to the source's exact cyclic construction.
Deliberate holes below are statement placeholders, never imported by Solution.
-/

open scoped BigOperators

universe u

namespace SparseMM
"""]
parts += [between(source("Masks"), "abbrev Mask", "theorem mask_card_eq_sum_rows")]
parts += [between(source("Masks"), "/-- Middle indices contributing", "/-- Potential residual products"),
          between(source("Masks"), "/-- Clustered outputs have zero weight", "theorem residualWeight_le")]
parts += [between(source("Rounding"), "def teamSize", "theorem teamSize_pos")]
parts += [theorem(source("Rounding"), "threshold_le_two_mul_sqrt")]
parts += ["end SparseMM\n\nnamespace SparseMM.Counting\n",
          between(source("Counting"), "def load", "theorem count_eq_load"),
          "end SparseMM.Counting\n\nnamespace SparseMM.Algebra\nvariable {I J K T R : Type*}\n",
          between(source("Algebra"), "/-- Every input coordinate", "/-- Potentially contributing"),
          "end SparseMM.Algebra\n\nnamespace SparseMM.HelperPlan\n",
          between(source("HelperPlan"), "abbrev Input", "abbrev Helper"),
          "end SparseMM.HelperPlan\n\nnamespace SparseMM.Routing\n",
          between(source("Routing"), "/-- A slot assignment", "private theorem schedule_subset"),
          "end SparseMM.Routing\n\nnamespace SparseMM\n"]
parts += [between(source("Clustering"), "variable {I K", "/-- Dense-rectangle extraction"),
          "/-- Complete finite clustering from public requested coordinates. -/\n",
          theorem(source("Clustering"), "exists_clustering"),
          "end SparseMM\n\n"]
parts += ["namespace SparseMM\n",
          "/-- Literal strict residual-output load guarantee, with an actual fixed assignment. -/\n",
          theorem(source("OutputPlan"), "exists_strict_output_plan"),
          "end SparseMM\n\n"]
model = source("Model")
parts += [between(model, "namespace SparseMM.Model", "omit [Fintype Packet] [DecidableEq Packet] in")]
for name in ("executeFrom_delivers", "exists_public_redistribution"):
    parts += [theorem(model, name)]
parts += [between(model, "/-- Packet labels of actual outgoing", "omit [DecidableEq Packet] in\n/-- Every actual execution")]
for name in ("actual_send_capacity", "actual_receive_capacity"):
    parts += ["omit [DecidableEq Packet] in\n", theorem(model, name)]
parts += ["end\nend Execution\nend SparseMM.Model\n\n"]
parts += ["namespace SparseMM.ExactRouting\nvariable {Packet Node : Type*} [DecidableEq Packet] [DecidableEq Node] [Fintype Node]\n",
          "/-- The source's exact regular-load redistribution schedule (Lemma 3). -/\n",
          theorem(source("ExactRouting"), "exists_schedule"),
          theorem(source("ExactRouting"), "exists_public_redistribution"),
          "end SparseMM.ExactRouting\n\n"]
parts += [between(source("LocalPipeline"), "namespace SparseMM.LocalPipeline", "/-- A phase is compatible"),
          "end SparseMM.LocalPipeline\n\n"]
parts += ["namespace SparseMM.Computation\nvariable {n : ℕ} {A B : Mask n} {S : Type*} [Semiring S]\n",
          between(source("Computation"), "/-- The mathematical value", "/-- Input-to-middle gathering"),
          "end SparseMM.Computation\n\n",
          "namespace SparseMM.SupportedProgram\nvariable {n : ℕ} {A B : Mask n} {S : Type*} [Semiring S]\n",
          between(source("Program"), "abbrev View", "noncomputable section"),
          "noncomputable section\n",
          between(source("Program"), "/-- The mathematical input instance", "def initialConfiguration"),
          "end\nend SparseMM.SupportedProgram\n\n"]
parts += ["namespace SparseMM.OutputAssignment\n",
          between(source("OutputAssignment"), "/-- The actual weighted load", "theorem sum_perm_fiber"),
          "/-- One public assignment balances counts and weighted contributions. -/\n",
          theorem(source("OutputAssignment"), "exists_balanced_output_assignment"),
          "end SparseMM.OutputAssignment\n\n"]
wire = source("Wire")
parts += [between(wire, "namespace SparseMM.Wire", "/-- Omitting packet labels"),
          theorem(wire, "receive_eq_model"),
          between(wire, "/-- Encode the one-value", "/-- Exact decoding is required"),
          theorem(wire, "encodedReceive_eq_model"),
          "end\nend SparseMM.Wire\n\n"]
parts += [between(source("Signatures"), "namespace SparseMM.Signatures", "end SparseMM.Signatures"),
          "end SparseMM.Signatures\n\nnamespace SparseMM\n",
          "/-- Theorem 4: one public program works for all supported numerical inputs. -/\n",
          theorem(source("Main"), "supported_sparse_mm"),
          "end SparseMM\n"]
lower = source("BroadcastLower")
broadcast_part = [between(lower, "namespace SparseMM.BroadcastLower", "theorem destinations_card_le"),
                  "/-- Robust broadcast influence lower bound, including adaptive addressing and silence. -/\n",
                  theorem(lower, "broadcast_requires_rounds"),
                  "end System\nend SparseMM.BroadcastLower\n\n"]
# Constructor anchors refer to the broadcast system, so insert its concrete
# definition and execution before all constructor aliases.
signature_index = next(i for i, part in enumerate(parts) if part.startswith("namespace SparseMM.Signatures"))
parts[signature_index:signature_index] = broadcast_part
aggregation_part = ["namespace SparseMM.BooleanDegree\nabbrev Cube (n : ℕ) := Fin n → Bool\nend SparseMM.BooleanDegree\n\n",
                    "namespace SparseMM.AggregationLower\nopen BooleanDegree\nvariable {n : ℕ} {State Message : Type*}\n",
                    between(source("AggregationLower"), "/-- Each processor's initial private state", "def stateAt"),
                    "/-- All-input legality and local private initial states force logarithmic OR aggregation. -/\n",
                    theorem(source("AggregationLower"), "or_requires_rounds"),
                    theorem(source("AggregationLower"), "and_requires_rounds"),
                    theorem(source("AggregationLower"), "sum_requires_rounds"),
                    "end SparseMM.AggregationLower\n\n"]
parts += aggregation_part
parts += ["namespace SparseMM.ToolboxComplexity\n",
          theorem(source("ToolboxComplexity"), "log_div_le_rounds"),
          theorem(source("ToolboxComplexity"), "clog_two_le_log_div_add_one"),
          theorem(source("ToolboxComplexity"), "pipeline_rounds_le"),
          theorem(source("ToolboxComplexity"), "single_value_rounds_le_log"),
          "end SparseMM.ToolboxComplexity\n\n"]
parts += ["namespace SparseMM.PipelinedBroadcast\n",
          "/-- One public local scalar system broadcasts every private source vector. -/\n",
          theorem(source("PipelinedBroadcast"), "exists_broadcast"),
          "end SparseMM.PipelinedBroadcast\n\nnamespace SparseMM.PipelinedAggregation\n",
          "/-- One public local scalar system aggregates every privately distributed vector. -/\n",
          theorem(source("PipelinedBroadcast"), "exists_aggregation"),
          "end SparseMM.PipelinedAggregation\n\n"]
parts += ["namespace SparseMM.BooleanAggregation\n",
          "/-- Boolean AND aggregation with literal Boolean messages and private local inputs. -/\n",
          theorem(source("BooleanAggregation"), "exists_and"),
          "/-- Boolean OR aggregation with literal Boolean messages and private local inputs. -/\n",
          theorem(source("BooleanAggregation"), "exists_or"),
          "end SparseMM.BooleanAggregation\n\n"]
challenge = "\n".join(parts).rstrip() + "\n"

config = {
    "challenge_module": "Challenge",
    "solution_module": "Solution",
    "theorem_names": [
        "SparseMM.exists_clustering",
        "SparseMM.threshold_le_two_mul_sqrt",
        "SparseMM.OutputAssignment.exists_balanced_output_assignment",
        "SparseMM.Model.executeFrom_delivers",
        "SparseMM.Model.exists_public_redistribution",
        "SparseMM.Model.actual_send_capacity",
        "SparseMM.Model.actual_receive_capacity",
        "SparseMM.ExactRouting.exists_schedule",
        "SparseMM.ExactRouting.exists_public_redistribution",
        "SparseMM.Wire.receive_eq_model",
        "SparseMM.Wire.encodedReceive_eq_model",
        "SparseMM.supported_sparse_mm",
        "SparseMM.BroadcastLower.System.broadcast_requires_rounds",
        "SparseMM.AggregationLower.or_requires_rounds",
        "SparseMM.AggregationLower.and_requires_rounds",
        "SparseMM.AggregationLower.sum_requires_rounds",
        "SparseMM.ToolboxComplexity.log_div_le_rounds",
        "SparseMM.ToolboxComplexity.clog_two_le_log_div_add_one",
        "SparseMM.ToolboxComplexity.pipeline_rounds_le",
        "SparseMM.ToolboxComplexity.single_value_rounds_le_log",
        "SparseMM.PipelinedBroadcast.exists_broadcast",
        "SparseMM.PipelinedAggregation.exists_aggregation",
        "SparseMM.exists_strict_output_plan",
        "SparseMM.BooleanAggregation.exists_and",
        "SparseMM.BooleanAggregation.exists_or",
    ],
    "definition_names": [
        "SparseMM.Mask", "SparseMM.rowMask", "SparseMM.colMask", "SparseMM.UniformSparse",
        "SparseMM.middleSet", "SparseMM.residualWeight",
        "SparseMM.teamSize", "SparseMM.threshold", "SparseMM.FitsRectangle", "SparseMM.ResidualSparse",
        "SparseMM.Counting.load", "SparseMM.Counting.count", "SparseMM.Algebra.SupportedBy",
        "SparseMM.HelperPlan.Input", "SparseMM.Routing.LegalOn", "SparseMM.Model.LocalState",
        "SparseMM.Model.Configuration", "SparseMM.Model.initial", "SparseMM.Model.outgoingLabel",
        "SparseMM.Model.incomingLabel", "SparseMM.Model.send", "SparseMM.Model.receive",
        "SparseMM.Model.accept", "SparseMM.Model.step", "SparseMM.Model.executeFrom", "SparseMM.Model.execute",
        "SparseMM.Model.transmitted",
        "SparseMM.LocalPipeline.Stage.run", "SparseMM.LocalPipeline.Program.rounds",
        "SparseMM.LocalPipeline.Program.execute", "SparseMM.LocalPipeline.Program.output",
        "SparseMM.Computation.inputValue", "SparseMM.SupportedProgram.View", "SparseMM.SupportedProgram.views",
        "SparseMM.OutputAssignment.weightedLoad", "SparseMM.OutputAssignment.assignedCount",
        "SparseMM.Wire.send", "SparseMM.Wire.receive", "SparseMM.Wire.encodedSend", "SparseMM.Wire.encodedReceive",
        "SparseMM.Signatures.StaticPlan_constructor", "SparseMM.Signatures.Stage_constructor",
        "SparseMM.Signatures.Program_constructor", "SparseMM.Signatures.Clustering_constructor",
        "SparseMM.Signatures.BroadcastSystem_constructor",
        "SparseMM.BroadcastLower.System.inbox", "SparseMM.BroadcastLower.System.LegalAt",
        "SparseMM.BroadcastLower.System.step", "SparseMM.BroadcastLower.System.execute",
        "SparseMM.BroadcastLower.changed", "SparseMM.BroadcastLower.System.destinations",
        "SparseMM.BooleanDegree.Cube", "SparseMM.AggregationLower.initialConfiguration",
    ],
    "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
}
outputs = {"Challenge.lean": challenge, "comparator.json": json.dumps(config, indent=2) + "\n"}
if sys.argv[1:] == ["--check"]:
    for name, content in outputs.items():
        if (ROOT / name).read_bytes() != content.encode("utf-8"):
            raise SystemExit(f"{name} differs from the generated interface")
    print("Challenge and Comparator configuration match the generated interface.")
elif not sys.argv[1:]:
    for name, content in outputs.items():
        (ROOT / name).write_text(content, encoding="utf-8", newline="\n")
    print(f"Generated {len(challenge.splitlines())} Challenge lines, "
          f"{len(config['theorem_names'])} theorem types and {len(config['definition_names'])} definitions.")
else:
    raise SystemExit("Usage: build_challenge.py [--check]")
