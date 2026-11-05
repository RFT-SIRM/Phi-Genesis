module
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
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


/-- For one indexed undirected edge, the sum of its incidence entries
over all vertices is zero in GF(2). Both endpoints contribute one, even
when the edge is a loop. -/
theorem incidenceEntry_sum_vertices_eq_zero
    {V E : Type*} [Fintype V] [DecidableEq V]
    (source target : E → V) (e : E) :
    (∑ v : V, incidenceEntry source target e v) = 0 := by
  classical
  norm_num [incidenceEntry, Finset.sum_add_distrib]
  exact ZMod.natCast_self 2



/-- Handshake parity for a finite indexed multigraph: the sum of all
vertex-degree parities is zero in GF(2), since every edge contributes
two incidences. -/
theorem incidenceDegreeParity_sum_vertices_eq_zero
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (source target : E → V) (F : Finset E) :
    (∑ v : V, incidenceDegreeParity source target F v) = 0 := by
  classical
  simp only [incidenceDegreeParity]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum]
  simp [incidenceEntry_sum_vertices_eq_zero]



/-- The reduced incidence column of an edge in a graph with an exterior
root. The endpoint `none` denotes the root, whose row is omitted. -/
def reducedIncidenceColumn (source target : E → Option V) (e : E) : V → ZMod 2 :=
  fun v => incidenceEntry source target e (some v)

/-- A finite edge-subset combination of reduced incidence columns is the
degree-parity function restricted to the non-root vertices. -/
theorem reducedIncidenceCombination_edgeIndicator
    (source target : E → Option V) (F : Finset E) :
    (∑ e : E, edgeIndicator F e • reducedIncidenceColumn source target e) =
      fun v => incidenceDegreeParity source target F (some v) := by
  classical
  ext v
  simp only [Finset.sum_apply, Pi.smul_apply, reducedIncidenceColumn,
    incidenceDegreeParity, smul_eq_mul]

/-- Removing the exterior-root row from a GF(2) incidence matrix preserves
column independence. The omitted root coordinate is forced by the
handshake-parity identity. The edge type remains indexed, so parallel edges
are not identified; loops remain zero columns and hence are dependent. -/
theorem reducedIncidenceColumns_linearIndependent_iff_forest
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (source target : E → Option V) :
    LinearIndependent (ZMod 2) (reducedIncidenceColumn source target) ↔
      IsIncidenceForest source target := by
  classical
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h F hF
    by_contra hNoOdd
    have hEven : ∀ v : Option V, incidenceDegreeParity source target F v = 0 := by
      intro v
      by_contra hv
      exact hNoOdd ⟨v, hv⟩
    have hzero :
        (∑ e : E, edgeIndicator F e • reducedIncidenceColumn source target e) = 0 := by
      rw [reducedIncidenceCombination_edgeIndicator]
      funext v
      exact hEven (some v)
    have hcoeff := h (edgeIndicator F) hzero
    obtain ⟨e, he⟩ := hF
    have hnonzero : edgeIndicator F e ≠ 0 := by
      simp [edgeIndicator, he]
    exact hnonzero (hcoeff e)
  · intro hForest c hzero
    by_contra hNotAllZero
    push Not at hNotAllZero
    obtain ⟨e, he⟩ := hNotAllZero
    let F : Finset E := Finset.univ.filter fun e => c e ≠ 0
    have hF : F.Nonempty := by
      refine ⟨e, ?_⟩
      simp [F, he]
    have hrep : c = edgeIndicator F := by
      simpa [F] using coefficient_eq_edgeIndicator c
    have hSome : ∀ v : V, incidenceDegreeParity source target F (some v) = 0 := by
      intro v
      have hpoint := congrFun hzero v
      rw [hrep] at hpoint
      simpa only [Finset.sum_apply, Pi.smul_apply, reducedIncidenceColumn,
        incidenceDegreeParity, smul_eq_mul, Pi.zero_apply] using hpoint
    have htotal :
        (∑ v : Option V, incidenceDegreeParity source target F v) = 0 :=
      incidenceDegreeParity_sum_vertices_eq_zero source target F
    rw [Fintype.sum_option] at htotal
    have hsumSome :
        (∑ v : V, incidenceDegreeParity source target F (some v)) = 0 := by
      simp [hSome]
    rw [hsumSome, add_zero] at htotal
    have hEven : ∀ v : Option V, incidenceDegreeParity source target F v = 0 := by
      intro v
      cases v with
      | none => exact htotal
      | some v => exact hSome v
    obtain ⟨v, hv⟩ := hForest F hF
    exact hv (hEven v)



/-- An incidence forest cannot contain a loop: a loop is already a
nonempty edge subset with even degree at every vertex. -/
theorem incidenceForest_no_loops
    {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (source target : E → V)
    (hForest : IsIncidenceForest source target) :
    ∀ e : E, source e ≠ target e := by
  classical
  intro e he
  let F : Finset E := {e}
  have hF : F.Nonempty := by simp [F]
  obtain ⟨v, hv⟩ := hForest F hF
  have hTwo : (1 : ZMod 2) + 1 = 0 := by
    calc
      (1 : ZMod 2) + 1 = (2 : ZMod 2) := by ring
      _ = 0 := ZMod.natCast_self 2
  have hEven : incidenceDegreeParity source target F v = 0 := by
    by_cases htv : target e = v
    · simp [F, incidenceDegreeParity, edgeIndicator, incidenceEntry,
        he, htv, hTwo]
    · simp [F, incidenceDegreeParity, edgeIndicator, incidenceEntry,
        he, htv]
  exact hv hEven



/-- Coefficients on a forest are uniquely determined by their incidence
sum. In particular, once a pivot edge set is known to be a forest, the
solution supported on that fixed set is unique. -/
theorem reducedIncidenceForest_coefficients_unique
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E]
    (source target : E → Option V)
    (hForest : IsIncidenceForest source target)
    (c d : E → ZMod 2)
    (hEq :
      (∑ e : E, c e • reducedIncidenceColumn source target e) =
      (∑ e : E, d e • reducedIncidenceColumn source target e)) :
    c = d := by
  classical
  have hLI :
      LinearIndependent (ZMod 2) (reducedIncidenceColumn source target) :=
    (reducedIncidenceColumns_linearIndependent_iff_forest source target).2 hForest
  rw [Fintype.linearIndependent_iff] at hLI
  have hzero :
      (∑ e : E, (c e - d e) • reducedIncidenceColumn source target e) = 0 := by
    calc
      (∑ e : E, (c e - d e) • reducedIncidenceColumn source target e)
          = ∑ e : E,
              (c e • reducedIncidenceColumn source target e -
                d e • reducedIncidenceColumn source target e) := by
              simp only [sub_smul]
      _ = (∑ e : E, c e • reducedIncidenceColumn source target e) -
          (∑ e : E, d e • reducedIncidenceColumn source target e) := by
            rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [hEq, sub_self]
  have hcoeff := hLI (fun e => c e - d e) hzero
  funext e
  exact sub_eq_zero.mp (hcoeff e)



/-- A forest cannot contain two distinct parallel edges. Over GF(2),
reversing an edge orientation leaves its incidence column unchanged, so
parallel indexed edges would give equal columns and violate independence. -/
theorem incidenceForest_no_parallel_edges
    {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (source target : E → V)
    (hForest : IsIncidenceForest source target) :
    ∀ e f : E, e ≠ f →
      (source e = source f ∧ target e = target f) ∨
      (source e = target f ∧ target e = source f) →
      False := by
  classical
  have hLI : LinearIndependent (ZMod 2) (incidenceColumn source target) :=
    (incidenceColumns_linearIndependent_iff_forest source target).2 hForest
  have hinj : Function.Injective (incidenceColumn source target) := hLI.injective
  intro e f hef hEndpoints
  apply hef
  apply hinj
  funext v
  rcases hEndpoints with hSame | hReverse
  · simp [incidenceColumn, incidenceEntry, hSame.1, hSame.2]
  · simp [incidenceColumn, incidenceEntry, hReverse.1, hReverse.2, add_comm]




/-- The reduced incidence columns of a forest form a basis whenever the
number of edges equals the number of non-root vertices. -/
noncomputable def reducedIncidenceForestBasis
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (source target : E → Option V)
    (hForest : IsIncidenceForest source target)
    (hCard : Fintype.card E = Fintype.card V) :
    Module.Basis E (ZMod 2) (V → ZMod 2) :=
  basisOfLinearIndependentOfCardEqFinrank
    ((reducedIncidenceColumns_linearIndependent_iff_forest source target).2 hForest)
    (by
      rw [Module.finrank_fintype_fun_eq_card]
      exact hCard)

/-- For a finite reduced-incidence forest with equally many edges and
non-root vertices, every right-hand side has exactly one edge-coefficient
solution over GF(2). -/
theorem reducedIncidenceForest_existsUnique_solution
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (source target : E → Option V)
    (hForest : IsIncidenceForest source target)
    (hCard : Fintype.card E = Fintype.card V)
    (rhs : V → ZMod 2) :
    ∃! c : E → ZMod 2,
      (∑ e : E, c e • reducedIncidenceColumn source target e) = rhs := by
  classical
  let B := reducedIncidenceForestBasis source target hForest hCard
  have hBasis :
      (∑ e : E, B.repr rhs e • reducedIncidenceColumn source target e) = rhs := by
    simpa [B, reducedIncidenceForestBasis] using B.sum_repr rhs
  refine ⟨B.repr rhs, hBasis, ?_⟩
  intro c hc
  apply reducedIncidenceForest_coefficients_unique source target hForest c (B.repr rhs)
  calc
    (∑ e : E, c e • reducedIncidenceColumn source target e) = rhs := hc
    _ = ∑ e : E, B.repr rhs e • reducedIncidenceColumn source target e := hBasis.symm




/-- The canonical GF(2) solver associated to a finite reduced-incidence
forest with equally many edges and non-root vertices. It sends each
right-hand side to its unique edge-coefficient vector. -/
noncomputable def reducedIncidenceForestSolverEquiv
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (source target : E → Option V)
    (hForest : IsIncidenceForest source target)
    (hCard : Fintype.card E = Fintype.card V) :
    (V → ZMod 2) ≃ₗ[ZMod 2] (E → ZMod 2) :=
  (reducedIncidenceForestBasis source target hForest hCard).equivFun

/-- Applying the canonical solver gives coefficients whose incidence
combination is exactly the prescribed right-hand side. -/
theorem reducedIncidenceForestSolverEquiv_spec
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (source target : E → Option V)
    (hForest : IsIncidenceForest source target)
    (hCard : Fintype.card E = Fintype.card V)
    (rhs : V → ZMod 2) :
    (∑ e : E,
      reducedIncidenceForestSolverEquiv source target hForest hCard rhs e •
        reducedIncidenceColumn source target e) = rhs := by
  simpa [reducedIncidenceForestSolverEquiv, reducedIncidenceForestBasis] using
    (reducedIncidenceForestBasis source target hForest hCard).sum_equivFun rhs

/-- The inverse of the canonical solver forms the incidence sum of a
coefficient vector. Thus the solver and the incidence map are inverse
linear equivalences, not merely a pointwise existence result. -/
theorem reducedIncidenceForestSolverEquiv_symm_apply
    {V E : Type*} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] [Nonempty E]
    (source target : E → Option V)
    (hForest : IsIncidenceForest source target)
    (hCard : Fintype.card E = Fintype.card V)
    (c : E → ZMod 2) :
    (reducedIncidenceForestSolverEquiv source target hForest hCard).symm c =
      ∑ e : E, c e • reducedIncidenceColumn source target e := by
  simpa [reducedIncidenceForestSolverEquiv, reducedIncidenceForestBasis] using
    (reducedIncidenceForestBasis source target hForest hCard).equivFun_symm_apply c




/-- A parent map whose parent always has strictly smaller natural rank
defines a rooted incidence forest. The proof uses a maximum-rank vertex
in any nonempty edge subset: no selected edge can enter that vertex from
a child, so its only selected incidence is its own parent edge. -/
theorem incidenceForest_of_rank_decreasing_parent
    {V : Type*} [Fintype V] [DecidableEq V]
    (rank : V → Nat) (parent : V → Option V)
    (hparent : ∀ v w, parent v = some w → rank w < rank v) :
    IsIncidenceForest (fun v : V => some v) parent := by
  classical
  intro F hF
  obtain ⟨v, hvF, hmax⟩ := Finset.exists_max_image F rank hF
  have hNoLoop : parent v ≠ some v := by
    intro hv
    exact (Nat.lt_irrefl (rank v)) (hparent v v hv)
  have hTerm (e : V) :
      edgeIndicator F e *
          incidenceEntry (fun x : V => some x) parent e (some v) =
        if e = v then 1 else 0 := by
    by_cases hev : e = v
    · subst e
      simp [edgeIndicator, hvF, incidenceEntry, hNoLoop]
    · by_cases heF : e ∈ F
      · have hNoIncoming : parent e ≠ some v := by
          intro hp
          have hlt : rank v < rank e := hparent e v hp
          exact (not_lt_of_ge (hmax e heF)) hlt
        simp [edgeIndicator, heF, incidenceEntry, hev, hNoIncoming]
      · simp [edgeIndicator, heF, hev]
  have hParity :
      incidenceDegreeParity (fun v : V => some v) parent F (some v) = 1 := by
    simp [incidenceDegreeParity, hTerm]
  refine ⟨some v, ?_⟩
  rw [hParity]
  norm_num

/-- Every strictly rank-decreasing parent system has a canonical GF(2)
solver: the reduced incidence matrix of its parent edges is invertible. -/
noncomputable def rankDecreasingParentSolverEquiv
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (rank : V → Nat) (parent : V → Option V)
    (hparent : ∀ v w, parent v = some w → rank w < rank v) :
    (V → ZMod 2) ≃ₗ[ZMod 2] (V → ZMod 2) :=
  reducedIncidenceForestSolverEquiv
    (fun v : V => some v) parent
    (incidenceForest_of_rank_decreasing_parent rank parent hparent)
    rfl

/-- The parent-tree solver coefficients reconstruct every prescribed
right-hand side exactly. -/
theorem rankDecreasingParentSolverEquiv_spec
    {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (rank : V → Nat) (parent : V → Option V)
    (hparent : ∀ v w, parent v = some w → rank w < rank v)
    (rhs : V → ZMod 2) :
    (∑ v : V,
      rankDecreasingParentSolverEquiv rank parent hparent rhs v •
        reducedIncidenceColumn (fun v : V => some v) parent v) = rhs := by
  simpa [rankDecreasingParentSolverEquiv] using
    (reducedIncidenceForestSolverEquiv_spec
      (fun v : V => some v) parent
      (incidenceForest_of_rank_decreasing_parent rank parent hparent)
      rfl rhs)


/-- The postorder address list used by the scalar H10 hole enumeration.
At level m + 1, each of the three child copies is listed recursively,
followed by the address of the parent cell. -/
def gasketAddressOrder : Nat → List (List (Fin 3))
  | 0 => []
  | m + 1 =>
      (gasketAddressOrder m).map (fun w => (0 : Fin 3) :: w) ++
      (gasketAddressOrder m).map (fun w => (1 : Fin 3) :: w) ++
      (gasketAddressOrder m).map (fun w => (2 : Fin 3) :: w) ++
      [[]]

/-- The recursive address list contains exactly the ternary words of
length strictly smaller than the level. -/
theorem mem_gasketAddressOrder_iff (m : Nat) (w : List (Fin 3)) :
    w ∈ gasketAddressOrder m ↔ w.length < m := by
  induction m generalizing w with
  | zero =>
      simp [gasketAddressOrder]
  | succ m ih =>
      cases w with
      | nil =>
          simp [gasketAddressOrder]
      | cons d tail =>
          fin_cases d <;> simp [gasketAddressOrder, ih]

/-- A level-m gasket address is a ternary word of length less than m. -/
abbrev GasketAddress (m : Nat) := {w : List (Fin 3) // w.length < m}

/-- The address type is finite, using the recursive enumeration above. -/
noncomputable instance gasketAddressFintype (m : Nat) :
    Fintype (GasketAddress m) := by
  classical
  exact Fintype.subtype (gasketAddressOrder m).toFinset (by
    intro w
    simpa using mem_gasketAddressOrder_iff m w)

/-- The prefix strictly before the rightmost digit 2, when such a digit
exists. The recursion scans from the right, so an earlier 2 is ignored
once a later one has been found. -/
def prefixBeforeLastTwo : List (Fin 3) → Option (List (Fin 3))
  | [] => none
  | d :: ds =>
      match prefixBeforeLastTwo ds with
      | some p => some (d :: p)
      | none => if d = 2 then some [] else none

/-- A prefix ending immediately before a 2 is strictly shorter. -/
theorem prefixBeforeLastTwo_length_lt {w p : List (Fin 3)}
    (h : prefixBeforeLastTwo w = some p) : p.length < w.length := by
  induction w generalizing p with
  | nil =>
      simp [prefixBeforeLastTwo] at h
  | cons d ds ih =>
      cases htail : prefixBeforeLastTwo ds with
      | none =>
          by_cases hd : d = 2
          · have hp : p = [] := by
              have hEq : (some [] : Option (List (Fin 3))) = some p := by
                simpa [prefixBeforeLastTwo, htail, hd] using h
              exact (Option.some.inj hEq).symm
            subst p
            simp
          · simp [prefixBeforeLastTwo, htail, hd] at h
      | some q =>
          have hp : p = d :: q := by
            have hEq : (some (d :: q) : Option (List (Fin 3))) = some p := by
              simpa [prefixBeforeLastTwo, htail] using h
            exact (Option.some.inj hEq).symm
          subst p
          have hq := ih (p := q) htail
          simpa using Nat.add_lt_add_right hq 1

/-- Appending a digit different from 2 does not change the prefix
before the rightmost 2. -/
theorem prefixBeforeLastTwo_append_digit (w : List (Fin 3))
    (d : Fin 3) (hd : d ≠ 2) :
    prefixBeforeLastTwo (w ++ [d]) = prefixBeforeLastTwo w := by
  induction w with
  | nil =>
      simp [prefixBeforeLastTwo, hd]
  | cons a tail ih =>
      simp [prefixBeforeLastTwo, ih]

/-- Appending any number of 1 digits does not change that prefix. -/
theorem prefixBeforeLastTwo_append_replicate_one (w : List (Fin 3))
    (k : Nat) :
    prefixBeforeLastTwo (w ++ List.replicate k (1 : Fin 3)) =
      prefixBeforeLastTwo w := by
  induction k generalizing w with
  | zero =>
      simp
  | succ k ih =>
      change prefixBeforeLastTwo (w ++ ([1] ++ List.replicate k (1 : Fin 3))) =
        prefixBeforeLastTwo w
      rw [← List.append_assoc]
      calc
        prefixBeforeLastTwo ((w ++ [1]) ++ List.replicate k (1 : Fin 3)) =
            prefixBeforeLastTwo (w ++ [1]) := ih (w := w ++ [1])
        _ = prefixBeforeLastTwo w :=
          prefixBeforeLastTwo_append_digit w 1 (by decide)

/-- The parent-address suffix 0 1 ... 1 contains no 2, so it
preserves the prefix before the rightmost 2. -/
theorem prefixBeforeLastTwo_append_parent_suffix (w : List (Fin 3))
    (k : Nat) :
    prefixBeforeLastTwo (w ++ [0] ++ List.replicate k (1 : Fin 3)) =
      prefixBeforeLastTwo w := by
  calc
    prefixBeforeLastTwo (w ++ [0] ++ List.replicate k (1 : Fin 3)) =
        prefixBeforeLastTwo (w ++ [0]) :=
      prefixBeforeLastTwo_append_replicate_one (w ++ [0]) k
    _ = prefixBeforeLastTwo w :=
      prefixBeforeLastTwo_append_digit w 0 (by decide)

/-- The number of digits equal to 2 in a ternary address. -/
def gasketTwoCount : List (Fin 3) → Nat
  | [] => 0
  | d :: ds => (if d = 2 then 1 else 0) + gasketTwoCount ds

/-- The number of digits equal to 2 is additive under concatenation. -/
theorem gasketTwoCount_append (w z : List (Fin 3)) :
    gasketTwoCount (w ++ z) = gasketTwoCount w + gasketTwoCount z := by
  induction w with
  | nil =>
      simp [gasketTwoCount]
  | cons d ds ih =>
      simp [gasketTwoCount, ih, Nat.add_assoc]

/-- A word with no rightmost 2 contains no digit equal to 2. -/
theorem gasketTwoCount_eq_zero_of_prefix_none {w : List (Fin 3)}
    (h : prefixBeforeLastTwo w = none) : gasketTwoCount w = 0 := by
  induction w with
  | nil =>
      simp [gasketTwoCount]
  | cons d ds ih =>
      cases htail : prefixBeforeLastTwo ds with
      | some p =>
          simp [prefixBeforeLastTwo, htail] at h
      | none =>
          by_cases hd : d = 2
          · simp [prefixBeforeLastTwo, htail, hd] at h
          · have hcount := ih htail
            simp [gasketTwoCount, hd, hcount]

/-- Removing the rightmost 2 and the suffix after it decreases the
number of 2 digits by exactly one. -/
theorem gasketTwoCount_eq_prefix_succ {w p : List (Fin 3)}
    (h : prefixBeforeLastTwo w = some p) :
    gasketTwoCount w = gasketTwoCount p + 1 := by
  induction w generalizing p with
  | nil =>
      simp [prefixBeforeLastTwo] at h
  | cons d ds ih =>
      cases htail : prefixBeforeLastTwo ds with
      | none =>
          by_cases hd : d = 2
          · have hp : p = [] := by
              have hEq : (some [] : Option (List (Fin 3))) = some p := by
                simpa [prefixBeforeLastTwo, htail, hd] using h
              exact (Option.some.inj hEq).symm
            subst p
            have hcount := gasketTwoCount_eq_zero_of_prefix_none htail
            simp [gasketTwoCount, hd, hcount]
          · simp [prefixBeforeLastTwo, htail, hd] at h
      | some q =>
          have hp : p = d :: q := by
            have hEq : (some (d :: q) : Option (List (Fin 3))) = some p := by
              simpa [prefixBeforeLastTwo, htail] using h
            exact (Option.some.inj hEq).symm
          subst p
          have hcount := ih (p := q) htail
          simp [gasketTwoCount, hcount, Nat.add_assoc]

/-- Every replicate of the digit 1 has no occurrences of 2. -/
theorem gasketTwoCount_replicate_one (k : Nat) :
    gasketTwoCount (List.replicate k (1 : Fin 3)) = 0 := by
  induction k with
  | zero =>
      simp [gasketTwoCount]
  | succ k ih =>
      simp [List.replicate_succ, gasketTwoCount, ih]

/-- Forgetting the proof component after Option.pmap into a subtype
recovers the original optional value. -/
private theorem option_map_subtype_val_pmap
    {α : Type*} {P : α → Prop} (o : Option α)
    (h : ∀ a, o = some a → P a) :
    Option.map (fun x : {a // P a} => x.1)
      (Option.pmap
        (fun a ha => (⟨a, ha⟩ : {a // P a})) o h) = o := by
  cases o <;> rfl

/-- The bounded form of the prefix before the rightmost 2.
The length proof is stored with the prefix, so downstream parent maps
are ordinary Option.map operations rather than dependent matches. -/
def prefixBeforeLastTwoBounded (w : List (Fin 3)) :
    Option {p : List (Fin 3) // p.length < w.length} :=
  Option.pmap
    (fun p hp => ⟨p, hp⟩)
    (prefixBeforeLastTwo w)
    (fun p h => prefixBeforeLastTwo_length_lt h)

/-- Forgetting the proof component of a bounded prefix recovers
the original optional list prefix. -/
theorem prefixBeforeLastTwoBounded_map_val (w : List (Fin 3)) :
    Option.map
      (fun p : {p : List (Fin 3) // p.length < w.length} => p.1)
      (prefixBeforeLastTwoBounded w) = prefixBeforeLastTwo w := by
  simpa [prefixBeforeLastTwoBounded] using
    (option_map_subtype_val_pmap
      (P := fun p : List (Fin 3) => p.length < w.length)
      (o := prefixBeforeLastTwo w)
      (h := fun p hp => prefixBeforeLastTwo_length_lt hp))

/-- The bounded prefix retains the original rightmost-2 characterization. -/
theorem prefixBeforeLastTwoBounded_val {w : List (Fin 3)}
    {p : {p : List (Fin 3) // p.length < w.length}}
    (h : prefixBeforeLastTwoBounded w = some p) :
    prefixBeforeLastTwo w = some p.1 := by
  have hMap := congrArg
    (Option.map
      (fun q : {q : List (Fin 3) // q.length < w.length} => q.1)) h
  calc
    prefixBeforeLastTwo w =
        Option.map
          (fun q : {q : List (Fin 3) // q.length < w.length} => q.1)
          (prefixBeforeLastTwoBounded w) :=
      (prefixBeforeLastTwoBounded_map_val w).symm
    _ = some p.1 := by simpa using hMap

/-- The exact H10 address parent rule. Internal addresses point to the
terminal address u 0 1^(m-|u|-2); terminal addresses point to the prefix
before their rightmost 2, or to the common exterior vertex. -/
def gasketAddressParent (m : Nat) (u : GasketAddress m) :
    Option (GasketAddress m) :=
  if h : u.1.length + 1 < m then
    some ⟨u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1, by
      have hlen :
          (u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1).length < m := by
        simp
        omega
      exact hlen⟩
  else
    Option.map
      (fun p : {p : List (Fin 3) // p.length < u.1.length} =>
        (⟨p.1, Nat.lt_trans p.2 u.2⟩ : GasketAddress m))
      (prefixBeforeLastTwoBounded u.1)

/-- The base rank counts the occurrences of the digit 2 in an address. -/
def gasketAddressBaseRank (w : List (Fin 3)) : Nat :=
  gasketTwoCount w

/-- The internal-parent suffix 0 1 ... 1 contains no 2, so appending it
preserves the base rank. -/
theorem gasketAddressBaseRank_append_parent_suffix (w : List (Fin 3))
    (k : Nat) :
    gasketAddressBaseRank (w ++ [0] ++ List.replicate k (1 : Fin 3)) =
      gasketAddressBaseRank w := by
  rw [gasketAddressBaseRank, gasketAddressBaseRank,
    gasketTwoCount_append, gasketTwoCount_append]
  simp [gasketTwoCount, gasketTwoCount_replicate_one]

/-- A well-founded rank for the actual H10 parent map.
An internal address has rank one more than its terminal parent.
A terminal address has at least two more rank units than the prefix
before its rightmost 2. -/
def gasketAddressRank (m : Nat) (u : GasketAddress m) : Nat :=
  2 * gasketAddressBaseRank u.1 + (if u.1.length + 1 < m then 1 else 0)

/-- Every H10 address-parent edge strictly decreases the explicit rank. -/
theorem gasketAddressParent_rank_lt (m : Nat)
    (u v : GasketAddress m)
    (h : gasketAddressParent m u = some v) :
    gasketAddressRank m v < gasketAddressRank m u := by
  classical
  by_cases hInternal : u.1.length + 1 < m
  · have hEq :
        (some (⟨u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1, by
          have hlen :
              (u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1).length < m := by
            simp
            omega
          exact hlen⟩ : GasketAddress m)) = some v := by
      simpa [gasketAddressParent, hInternal] using h
    have hAddr :
        (⟨u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1, by
          have hlen :
              (u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1).length < m := by
            simp
            omega
          exact hlen⟩ : GasketAddress m) = v :=
      Option.some.inj hEq
    have hValue :
        v.1 = u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1 :=
      (congrArg Subtype.val hAddr).symm
    have hParentLen :
        (u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1).length + 1 = m := by
      simp
      omega
    have hParentNotInternal :
        ¬ (u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1).length + 1 < m := by
      omega
    have hVNotInternal : ¬ v.1.length + 1 < m := by
      rw [hValue]
      exact hParentNotInternal
    have hBase :
        gasketAddressBaseRank
            (u.1 ++ [0] ++ List.replicate (m - u.1.length - 2) 1) =
          gasketAddressBaseRank u.1 :=
      gasketAddressBaseRank_append_parent_suffix u.1 (m - u.1.length - 2)
    have hVBase :
        gasketAddressBaseRank v.1 = gasketAddressBaseRank u.1 := by
      rw [hValue]
      exact hBase
    calc
      gasketAddressRank m v =
          2 * gasketAddressBaseRank u.1 := by
            simp [gasketAddressRank, hVBase, hVNotInternal]
      _ < 2 * gasketAddressBaseRank u.1 + 1 := by omega
      _ = gasketAddressRank m u := by
            simp [gasketAddressRank, hInternal]
  · have hTerminal : u.1.length + 1 = m := by omega
    have hTerminalNotInternal : ¬ u.1.length + 1 < m := by omega
    cases hBounded : prefixBeforeLastTwoBounded u.1 with
    | none =>
        simp [gasketAddressParent, hInternal, hBounded] at h
    | some p =>
        have hEq :
            (some (⟨p.1, Nat.lt_trans p.2 u.2⟩ : GasketAddress m)) = some v := by
          simpa [gasketAddressParent, hInternal, hBounded] using h
        have hAddr :
            (⟨p.1, Nat.lt_trans p.2 u.2⟩ : GasketAddress m) = v :=
          Option.some.inj hEq
        have hValue : v.1 = p.1 :=
          (congrArg Subtype.val hAddr).symm
        have hPrefixLen : p.1.length < u.1.length := p.2
        have hParentInternal : p.1.length + 1 < m := by
          omega
        have hPrefix :
            prefixBeforeLastTwo u.1 = some p.1 :=
          prefixBeforeLastTwoBounded_val hBounded
        have hBase :
            gasketAddressBaseRank u.1 =
              gasketAddressBaseRank p.1 + 1 := by
          simpa [gasketAddressBaseRank] using
            (gasketTwoCount_eq_prefix_succ hPrefix)
        calc
          gasketAddressRank m v =
              2 * gasketAddressBaseRank p.1 + 1 := by
                simp [gasketAddressRank, hValue, hParentInternal]
          _ < 2 * (gasketAddressBaseRank p.1 + 1) := by omega
          _ = gasketAddressRank m u := by
                simp [gasketAddressRank, hTerminalNotInternal, hBase]

/-- The address-parent multigraph is an incidence forest at every level.
This is the concrete Sierpiński address-tree instance of the generic
rank-decreasing parent theorem. -/
theorem gasketAddressParent_isForest (m : Nat) :
    IsIncidenceForest (fun u : GasketAddress m => some u)
      (gasketAddressParent m) := by
  classical
  apply incidenceForest_of_rank_decreasing_parent
    (gasketAddressRank m) (gasketAddressParent m)
  intro u v huv
  exact gasketAddressParent_rank_lt m u v huv

/-- The exact H10 address tree has a canonical GF(2) solver at every
positive level. Its edge set is indexed by the non-root addresses, so
the reduced incidence matrix is square and invertible. -/
noncomputable def gasketAddressTreeSolverEquiv (m : Nat) :
    (GasketAddress (m + 1) → ZMod 2) ≃ₗ[ZMod 2]
      (GasketAddress (m + 1) → ZMod 2) := by
  letI : Nonempty (GasketAddress (m + 1)) := ⟨⟨[], by simp⟩⟩
  exact rankDecreasingParentSolverEquiv
    (gasketAddressRank (m + 1)) (gasketAddressParent (m + 1))
    (gasketAddressParent_rank_lt (m + 1))

/-- The address-tree solver reconstructs every prescribed finite
generation right-hand side exactly. -/
theorem gasketAddressTreeSolverEquiv_spec (m : Nat)
    (rhs : GasketAddress (m + 1) → ZMod 2) :
    (∑ u : GasketAddress (m + 1),
      gasketAddressTreeSolverEquiv m rhs u •
        reducedIncidenceColumn (fun u : GasketAddress (m + 1) => some u)
          (gasketAddressParent (m + 1)) u) = rhs := by
  classical
  letI : Nonempty (GasketAddress (m + 1)) := ⟨⟨[], by simp⟩⟩
  simpa [gasketAddressTreeSolverEquiv] using
    (rankDecreasingParentSolverEquiv_spec
      (gasketAddressRank (m + 1)) (gasketAddressParent (m + 1))
      (gasketAddressParent_rank_lt (m + 1)) rhs)


/-! ## Algebraic row sums for the address-tree components

These lemmas formalize the cancellation in the proposed fundamental-cut
formula. They are stated for arbitrary hole-boundary rows B; they do not
assume an ordering of primal edges or identify a minimum edge. -/

/-- The triangular row transform at an address. Internal rows contain the
row itself and its three children; terminal rows contain only themselves. -/
def gasketBoundaryRowTransform {E : Type*}
    (B : List (Fin 3) → E → ZMod 2) (m : Nat)
    (w : List (Fin 3)) : E → ZMod 2 :=
  fun e =>
    if w.length + 1 < m then
      B w e + B (w ++ [0]) e + B (w ++ [1]) e + B (w ++ [2]) e
    else
      B w e

/-- Sum the transformed rows in a complete address subtree of depth k.
The recursion lists the root, followed by the three child subtrees. -/
def gasketAddressSubtreeRowSum {E : Type*}
    (B : List (Fin 3) → E → ZMod 2) (m : Nat) :
    Nat → List (Fin 3) → E → ZMod 2
  | 0, w, e =>
      gasketBoundaryRowTransform B m w e
  | k + 1, w, e =>
      gasketBoundaryRowTransform B m w e
        + gasketAddressSubtreeRowSum B m k (w ++ [0]) e
        + gasketAddressSubtreeRowSum B m k (w ++ [1]) e
        + gasketAddressSubtreeRowSum B m k (w ++ [2]) e

/-- The transformed rows telescope on a complete ternary subtree:
their sum is exactly the original row at its root. -/
theorem gasketAddressSubtreeRowSum_eq {E : Type*}
    (B : List (Fin 3) → E → ZMod 2) (m k : Nat) (w : List (Fin 3))
    (h : w.length + k = m - 1) :
    gasketAddressSubtreeRowSum B m k w = B w := by
  funext e
  induction k generalizing w with
  | zero =>
      have hlen : w.length + 1 = m := by omega
      simp [gasketAddressSubtreeRowSum, gasketBoundaryRowTransform, hlen]
  | succ k ih =>
      have hInternal : w.length + 1 < m := by omega
      have h0 : (w ++ [0]).length + k = m - 1 := by simp; omega
      have h1 : (w ++ [1]).length + k = m - 1 := by simp; omega
      have h2 : (w ++ [2]).length + k = m - 1 := by simp; omega
      change
        gasketBoundaryRowTransform B m w e
          + gasketAddressSubtreeRowSum B m k (w ++ [0]) e
          + gasketAddressSubtreeRowSum B m k (w ++ [1]) e
          + gasketAddressSubtreeRowSum B m k (w ++ [2]) e =
        B w e
      rw [ih (w ++ [0]) h0, ih (w ++ [1]) h1, ih (w ++ [2]) h2]
      simp [gasketBoundaryRowTransform, hInternal]
      ring

/-- Fundamental-cut row sum for a nonterminal address, using the component
shape {u} union u2{0,1,2}^{<= m-|u|-2}. -/
theorem gasketAddressNonterminalCutRows_sum {E : Type*}
    (B : List (Fin 3) → E → ZMod 2) (m : Nat) (u : List (Fin 3))
    (hInternal : u.length + 1 < m) :
    gasketBoundaryRowTransform B m u
      + gasketAddressSubtreeRowSum B m (m - u.length - 2) (u ++ [2]) =
        (fun e => B u e + B (u ++ [0]) e + B (u ++ [1]) e) := by
  have hDepth :
      (u ++ [2]).length + (m - u.length - 2) = m - 1 := by
    simp
    omega
  rw [gasketAddressSubtreeRowSum_eq B m (m - u.length - 2) (u ++ [2]) hDepth]
  funext e
  simp [gasketBoundaryRowTransform, hInternal]
  ring

/-- Fundamental-cut row sum for a terminal address w=v 0 1^k whose unique
internal child is v. The component shape is {w,v} union v2{0,1,2}^{<=m-|v|-2}. -/
theorem gasketAddressTerminalCutRows_sum {E : Type*}
    (B : List (Fin 3) → E → ZMod 2) (m : Nat)
    (v : List (Fin 3)) (k : Nat)
    (hInternal : v.length + 1 < m)
    (hTerminal :
      (v ++ [0] ++ List.replicate k (1 : Fin 3)).length + 1 = m) :
    gasketBoundaryRowTransform B m (v ++ [0] ++ List.replicate k (1 : Fin 3))
      + gasketBoundaryRowTransform B m v
      + gasketAddressSubtreeRowSum B m (m - v.length - 2) (v ++ [2]) =
        (fun e =>
          B (v ++ [0] ++ List.replicate k (1 : Fin 3)) e
            + B v e + B (v ++ [0]) e + B (v ++ [1]) e) := by
  have hDepth :
      (v ++ [2]).length + (m - v.length - 2) = m - 1 := by
    simp
    omega
  have hLeaf :
      ¬ (v ++ [0] ++ List.replicate k (1 : Fin 3)).length + 1 < m := by
    intro hlt
    rw [hTerminal] at hlt
    exact (Nat.lt_irrefl m) hlt
  rw [gasketAddressSubtreeRowSum_eq B m (m - v.length - 2) (v ++ [2]) hDepth]
  funext e
  simp [gasketBoundaryRowTransform, hInternal, hLeaf]
  ring


end PhiGenesis.H10
