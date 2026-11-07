import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurSlots

namespace PhiGenesis.SpectralGap

/-- Row of the shifted signless matrix applied to `x`. -/
noncomputable def sgShiftedRow (m : Nat) (lam : ℝ)
    (x : SGVertex m → ℝ) (v : SGVertex m) : ℝ :=
  ∑ w, (sgSignlessLaplacianMatrix m -
    lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) v w * x w

private theorem mem_childSet_iff (m : Nat) (k : Fin 3) (v : SGVertex (m + 1)) :
    v ∈ sgChildVertexSet m k ↔ ∃ w, sgChildVertex m k w = v := by
  simp [sgChildVertexSet]

private theorem fin3_ne_zero : ∀ k : Fin 3, k ≠ 0 → k = 1 ∨ k = 2 := by decide
private theorem fin3_ne_one : ∀ k : Fin 3, k ≠ 1 → k = 0 ∨ k = 2 := by decide
private theorem fin3_ne_two : ∀ k : Fin 3, k ≠ 2 → k = 0 ∨ k = 1 := by decide

/-- C: gluing child functions into a parent function, given consistency on shared vertices. -/
theorem sgGlue_exists (m : Nat) (f : Fin 3 → SGVertex m → ℝ)
    (hcons : ∀ i a j b, sgChildVertex m i a = sgChildVertex m j b → f i a = f j b) :
    ∃ x : SGVertex (m + 1) → ℝ, ∀ i a, x (sgChildVertex m i a) = f i a := by
  classical
  have hs := sgChildVertex_surjective_union m
  refine ⟨fun v => f (Classical.choose (hs v)).1 (Classical.choose (hs v)).2, ?_⟩
  intro i a
  exact hcons _ _ _ _ (Classical.choose_spec (hs (sgChildVertex m i a)))

/-- G1: entry identity, requiring only that the vertex lies in no other child. -/
theorem sgSignlessLaplacianMatrix_entry_of_notMemOthers
    (m : Nat) (i : Fin 3) (a b : SGVertex m)
    (hother : ∀ k : Fin 3, k ≠ i → sgChildVertex m i a ∉ sgChildVertexSet m k) :
    sgSignlessLaplacianMatrix (m + 1) (sgChildVertex m i a) (sgChildVertex m i b) =
      sgSignlessLaplacianMatrix m a b := by
  classical
  let edgeTerm (k : Fin 3) (p : (Fin m → Fin 3) × TriangleEdge) : ℝ :=
    sgEdgeIndicator (m + 1)
      (sgChildVertex m k (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).1,
       sgChildVertex m k (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).2)
      (sgChildVertex m i a) *
    sgEdgeIndicator (m + 1)
      (sgChildVertex m k (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).1,
       sgChildVertex m k (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).2)
      (sgChildVertex m i b)
  have hzero (k : Fin 3) (hki : k ≠ i) :
      (∑ p : (Fin m → Fin 3) × TriangleEdge, edgeTerm k p) = 0 := by
    apply Finset.sum_eq_zero
    intro p _
    have hinc :
        sgEdgeIndicator (m + 1)
          (sgChildVertex m k (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).1,
           sgChildVertex m k (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).2)
          (sgChildVertex m i a) = 0 :=
      sgEdgeIndicator_childEdge_eq_zero_of_not_mem m k
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).1
        (faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) p).2
        (sgChildVertex m i a) (hother k hki)
    simp [edgeTerm, hinc]
  have hmain :
      (∑ p : (Fin m → Fin 3) × TriangleEdge, edgeTerm i p) =
        sgSignlessLaplacianMatrix m a b := by
    rw [sgSignlessLaplacianMatrix_eq_slotSum]
    apply Finset.sum_congr rfl
    intro p _
    simp [edgeTerm, sgEdgeIndicator_child_map]
  rw [sgSignlessLaplacianMatrix_eq_childSlotSum, Fintype.sum_prod_type]
  change (∑ k : Fin 3, ∑ p : (Fin m → Fin 3) × TriangleEdge, edgeTerm k p) =
    sgSignlessLaplacianMatrix m a b
  rw [Finset.sum_eq_single i (fun k _ hk => hzero k hk)
    (fun h => absurd (Finset.mem_univ i) h)]
  exact hmain

/-- G1 shifted. -/
theorem sgShifted_entry_of_notMemOthers
    (m : Nat) (lam : ℝ) (i : Fin 3) (a b : SGVertex m)
    (hother : ∀ k : Fin 3, k ≠ i → sgChildVertex m i a ∉ sgChildVertexSet m k) :
    (sgSignlessLaplacianMatrix (m + 1) -
      lam • (1 : Matrix (SGVertex (m + 1)) (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) (sgChildVertex m i b) =
    (sgSignlessLaplacianMatrix m -
      lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) a b := by
  have hG := sgSignlessLaplacianMatrix_entry_of_notMemOthers m i a b hother
  by_cases h : a = b
  · subst h
    simp [Matrix.sub_apply, Matrix.one_apply, hG]
  · have hne : sgChildVertex m i a ≠ sgChildVertex m i b :=
      fun h' => h (sgChildVertex_injective m i h')
    simp [Matrix.sub_apply, Matrix.one_apply, hG, h, hne]

/-- G2: no coupling to vertices outside the child copy. -/
theorem sgShifted_outside_of_notMemOthers
    (m : Nat) (lam : ℝ) (i : Fin 3) (a : SGVertex m)
    (hother : ∀ k : Fin 3, k ≠ i → sgChildVertex m i a ∉ sgChildVertexSet m k)
    (v : SGVertex (m + 1)) (hv : v ∉ sgChildVertexSet m i) :
    (sgSignlessLaplacianMatrix (m + 1) -
      lam • (1 : Matrix (SGVertex (m + 1)) (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) v = 0 := by
  classical
  have hu : sgChildVertex m i a ∈ sgChildVertexSet m i :=
    (mem_childSet_iff m i _).2 ⟨a, rfl⟩
  have huv : sgChildVertex m i a ≠ v := by
    intro h
    apply hv
    rw [← h]
    exact hu
  have hQ : sgSignlessLaplacianMatrix (m + 1) (sgChildVertex m i a) v = 0 := by
    rw [sgSignlessLaplacianMatrix_eq_childSlotSum]
    apply Finset.sum_eq_zero
    intro q _
    rcases q with ⟨k, e⟩
    let endpoints := faceEdgeEndpoints (sgFaceA m) (sgFaceB m) (sgFaceC m) e
    by_cases hki : k = i
    · subst k
      have hvzero :
          sgEdgeIndicator (m + 1)
            (sgChildVertex m i endpoints.1, sgChildVertex m i endpoints.2) v = 0 :=
        sgEdgeIndicator_childEdge_eq_zero_of_not_mem m i endpoints.1 endpoints.2 v hv
      exact mul_eq_zero.mpr (Or.inr (by simpa [endpoints] using hvzero))
    · have huzero :
          sgEdgeIndicator (m + 1)
            (sgChildVertex m k endpoints.1, sgChildVertex m k endpoints.2)
            (sgChildVertex m i a) = 0 :=
        sgEdgeIndicator_childEdge_eq_zero_of_not_mem m k endpoints.1 endpoints.2
          (sgChildVertex m i a) (hother k hki)
      exact mul_eq_zero.mpr (Or.inl (by simpa [endpoints] using huzero))
  simp [Matrix.sub_apply, Matrix.one_apply, hQ, huv]

/-- G3: the parent row at a vertex belonging to exactly one child is that child's row. -/
theorem sgShiftedRow_child_of_notMemOthers
    (m : Nat) (lam : ℝ) (i : Fin 3) (a : SGVertex m)
    (hother : ∀ k : Fin 3, k ≠ i → sgChildVertex m i a ∉ sgChildVertexSet m k)
    (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x (sgChildVertex m i a) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m i v)) a := by
  classical
  unfold sgShiftedRow
  let A : Finset (SGVertex (m + 1)) := sgChildVertexSet m i
  let f : SGVertex (m + 1) → ℝ := fun v =>
    (sgSignlessLaplacianMatrix (m + 1) -
      lam • (1 : Matrix (SGVertex (m + 1)) (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) v * x v
  have hdisj : Disjoint A ((Finset.univ : Finset (SGVertex (m + 1))) \ A) := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvComp
    exact (Finset.mem_sdiff.mp hvComp).2 hvA
  have hcover : A ∪ ((Finset.univ : Finset (SGVertex (m + 1))) \ A) = Finset.univ := by
    ext v
    simp [A]
  have hOutside :
      (∑ v ∈ (Finset.univ : Finset (SGVertex (m + 1))) \ A, f v) = 0 := by
    apply Finset.sum_eq_zero
    intro v hv
    have hvnot : v ∉ sgChildVertexSet m i := by
      simpa [A] using (Finset.mem_sdiff.mp hv).2
    change ((sgSignlessLaplacianMatrix (m + 1) -
      lam • (1 : Matrix (SGVertex (m + 1)) (SGVertex (m + 1)) ℝ))
      (sgChildVertex m i a) v) * x v = 0
    rw [sgShifted_outside_of_notMemOthers m lam i a hother v hvnot]
    simp
  have hi : Set.InjOn (sgChildVertex m i) (↑(Finset.univ : Finset (SGVertex m))) := by
    intro u _ v _ huv
    exact sgChildVertex_injective m i huv
  have hImage : (∑ b : SGVertex m, f (sgChildVertex m i b)) = (∑ v ∈ A, f v) := by
    dsimp [A, sgChildVertexSet]
    rw [Finset.sum_image hi]
  have hInside :
      (∑ v ∈ A, f v) =
        (∑ b : SGVertex m,
          (sgSignlessLaplacianMatrix m -
            lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) a b *
            x (sgChildVertex m i b)) := by
    rw [← hImage]
    apply Finset.sum_congr rfl
    intro b _
    change ((sgSignlessLaplacianMatrix (m + 1) -
        lam • (1 : Matrix (SGVertex (m + 1)) (SGVertex (m + 1)) ℝ))
        (sgChildVertex m i a) (sgChildVertex m i b)) * x (sgChildVertex m i b) =
      ((sgSignlessLaplacianMatrix m -
        lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) a b) * x (sgChildVertex m i b)
    rw [sgShifted_entry_of_notMemOthers m lam i a b hother]
  have hTotal :
      (∑ v : SGVertex (m + 1), f v) =
        (∑ v ∈ A, f v) +
          (∑ v ∈ (Finset.univ : Finset (SGVertex (m + 1))) \ A, f v) := by
    calc
      _ = (∑ v ∈ A ∪ ((Finset.univ : Finset (SGVertex (m + 1))) \ A), f v) := by
            rw [hcover]
      _ = _ := Finset.sum_union hdisj
  calc
    _ = (∑ v ∈ A, f v) +
          (∑ v ∈ (Finset.univ : Finset (SGVertex (m + 1))) \ A, f v) := hTotal
    _ = ∑ v ∈ A, f v := by rw [hOutside]; simp
    _ = _ := hInside

/-! ### Outer corners of the parent belong to exactly one child -/

private theorem outer_left_val (m : Nat) :
    (sgLevelOuterCorner m TriangleCorner.leftBase).1 = (0, 0) := by
  exact sgFaceCornerCoords_all_zero_left m

private theorem outer_right_val (m : Nat) :
    (sgLevelOuterCorner m TriangleCorner.rightBase).1 = (2 ^ m, 0) := by
  exact sgFaceCornerCoords_all_one_right m

private theorem outer_apex_val (m : Nat) :
    (sgLevelOuterCorner m TriangleCorner.apex).1 = (0, 2 ^ m) := by
  exact sgFaceCornerCoords_all_two_apex m

theorem sgOuterLeft_notMemOthers (m : Nat) :
    ∀ k : Fin 3, k ≠ 0 →
      sgChildVertex m 0 (sgLevelOuterCorner m TriangleCorner.leftBase) ∉
        sgChildVertexSet m k := by
  intro k hk hmem
  obtain ⟨w, hw⟩ := (mem_childSet_iff m k _).1 hmem
  have hpos : 0 < 2 ^ m := by positivity
  have hu := outer_left_val m
  rcases fin3_ne_zero k hk with rfl | rfl
  · have h := (sgChildVertex_intersection_zero_one_iff m _ w).1 hw.symm
    have e : ((0 : ℕ), (0 : ℕ)) = (2 ^ m, 0) := hu.symm.trans h.1
    have e1 : (0 : ℕ) = 2 ^ m := congrArg Prod.fst e
    exact hpos.ne e1
  · have h := (sgChildVertex_intersection_zero_two_iff m _ w).1 hw.symm
    have e : ((0 : ℕ), (0 : ℕ)) = (0, 2 ^ m) := hu.symm.trans h.1
    have e1 : (0 : ℕ) = 2 ^ m := congrArg Prod.snd e
    exact hpos.ne e1

theorem sgOuterRight_notMemOthers (m : Nat) :
    ∀ k : Fin 3, k ≠ 1 →
      sgChildVertex m 1 (sgLevelOuterCorner m TriangleCorner.rightBase) ∉
        sgChildVertexSet m k := by
  intro k hk hmem
  obtain ⟨w, hw⟩ := (mem_childSet_iff m k _).1 hmem
  have hpos : 0 < 2 ^ m := by positivity
  have hu := outer_right_val m
  rcases fin3_ne_one k hk with rfl | rfl
  · have h := (sgChildVertex_intersection_zero_one_iff m w _).1 hw
    have e : (2 ^ m, (0 : ℕ)) = (0, 0) := hu.symm.trans h.2
    have e1 : 2 ^ m = (0 : ℕ) := congrArg Prod.fst e
    exact hpos.ne' e1
  · have h := (sgChildVertex_intersection_one_two_iff m _ w).1 hw.symm
    have e : (2 ^ m, (0 : ℕ)) = (0, 2 ^ m) := hu.symm.trans h.1
    have e1 : 2 ^ m = (0 : ℕ) := congrArg Prod.fst e
    exact hpos.ne' e1

theorem sgOuterApex_notMemOthers (m : Nat) :
    ∀ k : Fin 3, k ≠ 2 →
      sgChildVertex m 2 (sgLevelOuterCorner m TriangleCorner.apex) ∉
        sgChildVertexSet m k := by
  intro k hk hmem
  obtain ⟨w, hw⟩ := (mem_childSet_iff m k _).1 hmem
  have hpos : 0 < 2 ^ m := by positivity
  have hu := outer_apex_val m
  rcases fin3_ne_two k hk with rfl | rfl
  · have h := (sgChildVertex_intersection_zero_two_iff m w _).1 hw
    have e : ((0 : ℕ), 2 ^ m) = (0, 0) := hu.symm.trans h.2
    have e1 : 2 ^ m = (0 : ℕ) := congrArg Prod.snd e
    exact hpos.ne' e1
  · have h := (sgChildVertex_intersection_one_two_iff m w _).1 hw
    have e : ((0 : ℕ), 2 ^ m) = (2 ^ m, 0) := hu.symm.trans h.2
    have e1 : (0 : ℕ) = 2 ^ m := congrArg Prod.fst e
    exact hpos.ne e1

/-- A: rows at the three outer corners of the parent are the child rows. -/
theorem sgShiftedRow_outerLeft (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x
        (sgChildVertex m 0 (sgLevelOuterCorner m TriangleCorner.leftBase)) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 0 v))
        (sgLevelOuterCorner m TriangleCorner.leftBase) :=
  sgShiftedRow_child_of_notMemOthers m lam 0 _ (sgOuterLeft_notMemOthers m) x

theorem sgShiftedRow_outerRight (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x
        (sgChildVertex m 1 (sgLevelOuterCorner m TriangleCorner.rightBase)) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 1 v))
        (sgLevelOuterCorner m TriangleCorner.rightBase) :=
  sgShiftedRow_child_of_notMemOthers m lam 1 _ (sgOuterRight_notMemOthers m) x

theorem sgShiftedRow_outerApex (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x
        (sgChildVertex m 2 (sgLevelOuterCorner m TriangleCorner.apex)) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 2 v))
        (sgLevelOuterCorner m TriangleCorner.apex) :=
  sgShiftedRow_child_of_notMemOthers m lam 2 _ (sgOuterApex_notMemOthers m) x

/-- D: shared vertices of two children are shared corners with the same boundary index. -/
theorem sgChildVertex_eq_cases (m : Nat) (i j : Fin 3) (a b : SGVertex m)
    (h : sgChildVertex m i a = sgChildVertex m j b) :
    (i = j ∧ a = b) ∨
      ∃ c c' : TriangleCorner,
        a = sgLevelOuterCorner m c ∧ b = sgLevelOuterCorner m c' ∧
          sgChildCornerBoundaryIndex i c = sgChildCornerBoundaryIndex j c' := by
  sorry

/-- B: row at midpoint 01 is the sum of the two child corner rows plus `lam * x(mid)`. -/
theorem sgShiftedRow_midpoint01 (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x (sgParentMidpoint01 m) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 0 v))
        (sgLevelOuterCorner m TriangleCorner.rightBase) +
      sgShiftedRow m lam (fun v => x (sgChildVertex m 1 v))
        (sgLevelOuterCorner m TriangleCorner.leftBase) +
      lam * x (sgParentMidpoint01 m) := by
  sorry

theorem sgShiftedRow_midpoint02 (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x (sgParentMidpoint02 m) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 0 v))
        (sgLevelOuterCorner m TriangleCorner.apex) +
      sgShiftedRow m lam (fun v => x (sgChildVertex m 2 v))
        (sgLevelOuterCorner m TriangleCorner.leftBase) +
      lam * x (sgParentMidpoint02 m) := by
  sorry

theorem sgShiftedRow_midpoint12 (m : Nat) (lam : ℝ) (x : SGVertex (m + 1) → ℝ) :
    sgShiftedRow (m + 1) lam x (sgParentMidpoint12 m) =
      sgShiftedRow m lam (fun v => x (sgChildVertex m 1 v))
        (sgLevelOuterCorner m TriangleCorner.apex) +
      sgShiftedRow m lam (fun v => x (sgChildVertex m 2 v))
        (sgLevelOuterCorner m TriangleCorner.rightBase) +
      lam * x (sgParentMidpoint12 m) := by
  sorry

end PhiGenesis.SpectralGap
