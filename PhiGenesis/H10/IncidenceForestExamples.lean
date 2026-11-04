module
import PhiGenesis.H10.IncidenceForest
import Mathlib.Tactic

/-!
# Regression examples for the GF(2) incidence/forest theorem

These examples deliberately retain indexed parallel edges and loops.
They guard against accidentally replacing the multigraph by a simple graph.
-/

namespace PhiGenesis.H10

/-- Reversing the endpoint order does not change an undirected incidence entry. -/
theorem incidenceEntry_endpoint_swap
    {V E : Type*} (source target : E → V) (e : E) (v : V) :
    incidenceEntry source target e v = incidenceEntry target source e v := by
  simp [incidenceEntry, add_comm]

/-- Reversing every edge orientation leaves the incidence column unchanged. -/
theorem incidenceColumn_endpoint_swap
    {V E : Type*} (source target : E → V) (e : E) :
    incidenceColumn source target e = incidenceColumn target source e := by
  funext v
  exact incidenceEntry_endpoint_swap source target e v

/-- Consequently the linear-independence criterion is orientation-independent. -/
theorem incidenceColumns_orientation_invariant
    {V E : Type*} [Fintype E] [DecidableEq E] [DecidableEq V]
    (source target : E → V) :
    LinearIndependent (ZMod 2) (incidenceColumn source target) ↔
      LinearIndependent (ZMod 2) (incidenceColumn target source) := by
  rw [incidenceColumns_linearIndependent_iff_forest,
    incidenceColumns_linearIndependent_iff_forest]
  constructor <;> intro h F hF
  · obtain ⟨v, hv⟩ := h F hF
    exact ⟨v, by simpa [incidenceDegreeParity, incidenceEntry, add_comm] using hv⟩
  · obtain ⟨v, hv⟩ := h F hF
    exact ⟨v, by simpa [incidenceDegreeParity, incidenceEntry, add_comm] using hv⟩

/-- Two distinct indexed edges with the same endpoints are parallel edges. -/
def parallelSource (e : Fin 2) : Fin 2 := 0

def parallelTarget (e : Fin 2) : Fin 2 := 1

/-- The pair of parallel edges is not an incidence forest. -/
theorem parallelPair_not_forest : ¬ IsIncidenceForest parallelSource parallelTarget := by
  intro h
  obtain ⟨v, hv⟩ := h Finset.univ Finset.univ_nonempty
  fin_cases v <;>
    norm_num [incidenceDegreeParity, edgeIndicator, incidenceEntry,
      parallelSource, parallelTarget] at hv

/-- Therefore the two parallel incidence columns are dependent. -/
theorem parallelPair_not_linearIndependent :
    ¬ LinearIndependent (ZMod 2) (incidenceColumn parallelSource parallelTarget) := by
  intro h
  exact parallelPair_not_forest
    ((incidenceColumns_linearIndependent_iff_forest parallelSource parallelTarget).mp h)

/-- A single loop has a zero incidence column over GF(2). -/
def loopEndpoint (e : Fin 1) : Fin 1 := 0

/-- The one-loop multigraph is not an incidence forest. -/
theorem loop_not_forest : ¬ IsIncidenceForest loopEndpoint loopEndpoint := by
  intro h
  obtain ⟨v, hv⟩ := h Finset.univ Finset.univ_nonempty
  fin_cases v
  norm_num [incidenceDegreeParity, edgeIndicator, incidenceEntry, loopEndpoint] at hv

/-- The zero column associated with a loop is linearly dependent. -/
theorem loop_not_linearIndependent :
    ¬ LinearIndependent (ZMod 2) (incidenceColumn loopEndpoint loopEndpoint) := by
  intro h
  exact loop_not_forest
    ((incidenceColumns_linearIndependent_iff_forest loopEndpoint loopEndpoint).mp h)

/-- The one-edge graph on two vertices is a forest. -/
def singleEdgeSource (e : Fin 1) : Fin 2 := 0

def singleEdgeTarget (e : Fin 1) : Fin 2 := 1

theorem singleEdge_is_forest :
    IsIncidenceForest singleEdgeSource singleEdgeTarget := by
  intro F hF
  obtain ⟨e, he⟩ := hF
  fin_cases e
  refine ⟨0, ?_⟩
  norm_num [incidenceDegreeParity, edgeIndicator, incidenceEntry,
    singleEdgeSource, singleEdgeTarget, he]

/-- The incidence column of a single non-loop edge is independent. -/
theorem singleEdge_linearIndependent :
    LinearIndependent (ZMod 2) (incidenceColumn singleEdgeSource singleEdgeTarget) :=
  (incidenceColumns_linearIndependent_iff_forest
    singleEdgeSource singleEdgeTarget).mpr singleEdge_is_forest

end PhiGenesis.H10
