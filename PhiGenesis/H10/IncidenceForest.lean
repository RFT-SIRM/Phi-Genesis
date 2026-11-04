module
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.Tactic

/-!
# Incidence matrices over GF(2)

Edges are indexed by a finite type, so parallel edges remain distinct.
The two endpoints are counted separately; consequently a loop contributes
twice at its vertex and has a zero incidence column over ZMod 2.

For a finite undirected multigraph, the condition that every nonempty edge
subset has a vertex of odd degree is the standard even-subgraph
characterization of a forest. It detects loops and two-edge cycles formed
by parallel edges.
-/

namespace PhiGenesis.H10

variable {V E : Type*}
variable [DecidableEq V]
variable [Fintype E] [DecidableEq E]

/-- The contribution of one indexed edge to the degree parity at a vertex. -/
def incidenceEntry (source target : E → V) (e : E) (v : V) : ZMod 2 :=
  (if source e = v then 1 else 0) + (if target e = v then 1 else 0)

/-- The GF(2) incidence column of an indexed edge. -/
def incidenceColumn (source target : E → V) (e : E) : V → ZMod 2 :=
  fun v => incidenceEntry source target e v

/-- The indicator of a finite set of indexed edges, viewed over GF(2). -/
def edgeIndicator (F : Finset E) (e : E) : ZMod 2 :=
  if e ∈ F then 1 else 0

/-- The parity of the degree of v in the edge subset F.
Both endpoints are counted, so a loop contributes two incidences.
-/
def incidenceDegreeParity (source target : E → V) (F : Finset E) (v : V) : ZMod 2 :=
  ∑ e : E, edgeIndicator F e * incidenceEntry source target e v

/-- Finite even-subgraph characterization of a forest for an indexed multigraph. -/
def IsIncidenceForest (source target : E → V) : Prop :=
  ∀ F : Finset E, F.Nonempty → ∃ v : V, incidenceDegreeParity source target F v ≠ 0

/-- Every element of ZMod 2 is either zero or one. -/
theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A ZMod 2 coefficient function is the indicator of its nonzero support. -/
theorem coefficient_eq_edgeIndicator (c : E → ZMod 2) :
    c = edgeIndicator (Finset.univ.filter fun e => c e ≠ 0) := by
  classical
  funext e
  by_cases he : c e = 0
  · simp [edgeIndicator, he]
  · have hc : c e = 1 := by
      rcases zmod_two_eq_zero_or_one (c e) with hzero | hone
      · exact (he hzero).elim
      · exact hone
    have hmem : e ∈ Finset.univ.filter (fun e => c e ≠ 0) := by
      simp [hc]
    simp [edgeIndicator, hmem, hc]

/-- The linear combination with coefficients 1_F is the degree-parity function. -/
theorem incidenceCombination_edgeIndicator
    (source target : E → V) (F : Finset E) :
    (∑ e : E, edgeIndicator F e • incidenceColumn source target e) =
      fun v => incidenceDegreeParity source target F v := by
  classical
  ext v
  simp only [Finset.sum_apply, Pi.smul_apply, incidenceColumn, incidenceDegreeParity, smul_eq_mul]

/-- The indexed incidence columns over GF(2) are linearly independent
iff every nonempty edge subset has a vertex of odd degree.

This is the incidence-matrix/forest theorem for finite undirected multigraphs.
Parallel edges are retained by the edge index type; loops have zero columns.
-/
theorem incidenceColumns_linearIndependent_iff_forest
    (source target : E → V) :
    LinearIndependent (ZMod 2) (incidenceColumn source target) ↔
      IsIncidenceForest source target := by
  classical
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h F hF
    by_contra hNoOdd
    have hEven : ∀ v : V, incidenceDegreeParity source target F v = 0 := by
      intro v
      by_contra hv
      exact hNoOdd ⟨v, hv⟩
    let c : E → ZMod 2 := edgeIndicator F
    have hzero :
        (∑ e : E, c e • incidenceColumn source target e) = 0 := by
      rw [incidenceCombination_edgeIndicator]
      funext v
      exact hEven v
    have hcoeff := h c hzero
    obtain ⟨e, he⟩ := hF
    have hnonzero : c e ≠ 0 := by
      simp [c, edgeIndicator, he]
    exact hnonzero (hcoeff e)
  · intro hForest c hzero
    by_contra hNotAllZero
    push Not at hNotAllZero
    obtain ⟨e, he⟩ := hNotAllZero
    let F : Finset E := Finset.univ.filter fun e => c e ≠ 0
    have hF : F.Nonempty := by
      refine ⟨e, ?_⟩
      simp [F, he]
    obtain ⟨v, hv⟩ := hForest F hF
    have hrep : c = edgeIndicator F := by
      simpa [F] using coefficient_eq_edgeIndicator c
    rw [hrep] at hzero
    have hpoint := congrFun hzero v
    rw [incidenceCombination_edgeIndicator] at hpoint
    exact hv hpoint


/-- The finite even-subgraph criterion is invariant under reversing edge orientations. -/
theorem incidenceForest_orientation_invariant
    {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (source target : E → V) :
    IsIncidenceForest source target ↔ IsIncidenceForest target source := by
  constructor <;> intro h F hF
  · obtain ⟨v, hv⟩ := h F hF
    refine ⟨v, ?_⟩
    simpa [incidenceDegreeParity, incidenceEntry, add_comm] using hv
  · obtain ⟨v, hv⟩ := h F hF
    refine ⟨v, ?_⟩
    simpa [incidenceDegreeParity, incidenceEntry, add_comm] using hv

end PhiGenesis.H10

