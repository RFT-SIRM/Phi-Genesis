import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurSlots
import PhiGenesis.SpectralGap.SchurGlueAlgebra
import PhiGenesis.SpectralGap.SchurBridgeLevelZero
import PhiGenesis.SpectralGap.SchurGlueRows

namespace PhiGenesis.SpectralGap

/-- `(a, b)` is the corner response of the shifted signless matrix at level `m`. -/
def SgCornerResponse (m : Nat) (lam a b : ℝ) : Prop :=
  ∀ z : TriangleCorner → ℝ, ∃ x : SGVertex m → ℝ,
    (∀ c, x (sgLevelOuterCorner m c) = z c) ∧
    (∀ v : SGVertex m, (∀ c, v ≠ sgLevelOuterCorner m c) →
      ∑ w, (sgSignlessLaplacianMatrix m -
        lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) v w * x w = 0) ∧
    (∀ c, ∑ w, (sgSignlessLaplacianMatrix m -
        lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) (sgLevelOuterCorner m c) w * x w =
      a * z c + b * (∑ c', z c' - z c))

/-- At level 0 the outer corner does not depend on the (unique) face address. -/
private theorem outer0_eq (f : Fin 0 → Fin 3) (c : TriangleCorner) :
    sgLevelOuterCorner 0 c = sgCornerVertex 0 (f, c) := by
  cases c
  · exact congrArg
      (fun g : Fin 0 → Fin 3 => sgCornerVertex 0 (g, TriangleCorner.leftBase))
      (Subsingleton.elim _ _)
  · exact congrArg
      (fun g : Fin 0 → Fin 3 => sgCornerVertex 0 (g, TriangleCorner.rightBase))
      (Subsingleton.elim _ _)
  · exact congrArg
      (fun g : Fin 0 → Fin 3 => sgCornerVertex 0 (g, TriangleCorner.apex))
      (Subsingleton.elim _ _)

private theorem outer0_injective : Function.Injective (sgLevelOuterCorner 0) := by
  intro c c' h
  have hv := congrArg (fun v : SGVertex 0 => v.1) h
  cases c <;> cases c' <;>
    simp [sgLevelOuterCorner, sgCornerVertex, sgFaceCornerCoords,
      sgFaceOrigin] at hv ⊢

private theorem outer0_surjective : Function.Surjective (sgLevelOuterCorner 0) := by
  intro v
  obtain ⟨⟨f, c⟩, hfc⟩ := sgCornerVertex_surjective 0 v
  exact ⟨c, (outer0_eq f c).trans hfc⟩

/-- Base case: level 0 has response `(2 - lam, 1)` (step B1). -/
theorem sgCornerResponse_zero (lam : ℝ) : SgCornerResponse 0 lam (2 - lam) 1 := by
  classical
  intro z
  let e : TriangleCorner ≃ SGVertex 0 :=
    Equiv.ofBijective (sgLevelOuterCorner 0) ⟨outer0_injective, outer0_surjective⟩
  have he : ∀ c, e c = sgLevelOuterCorner 0 c := fun c => rfl
  have hx : ∀ c, z (e.symm (sgLevelOuterCorner 0 c)) = z c := by
    intro c
    rw [← he c, e.symm_apply_apply]
  have hsum : ∑ w : SGVertex 0, z (e.symm w) = ∑ c, z c :=
    Equiv.sum_comp e.symm z
  refine ⟨fun v => z (e.symm v), hx, ?_, ?_⟩
  · intro v hv
    obtain ⟨c, hc⟩ := outer0_surjective v
    exact absurd hc.symm (hv c)
  · intro c
    have hterm : ∀ w : SGVertex 0,
        (sgSignlessLaplacianMatrix 0 -
          lam • (1 : Matrix (SGVertex 0) (SGVertex 0) ℝ)) (sgLevelOuterCorner 0 c) w *
            z (e.symm w) =
          z (e.symm w) +
            (if sgLevelOuterCorner 0 c = w
              then (1 - lam) * z (e.symm w) else 0) := by
      intro w
      rw [sgSignlessShifted_zero]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl (fun w _ => hterm w), Finset.sum_add_distrib,
      Finset.sum_ite_eq, if_pos (Finset.mem_univ _), hsum, hx c]
    ring

/-! ### Induction step: helper lemmas -/

private noncomputable def crData (b c : ℝ) (z : TriangleCorner → ℝ) : Fin 6 → ℝ
  | 0 => z TriangleCorner.leftBase
  | 1 => z TriangleCorner.rightBase
  | 2 => z TriangleCorner.apex
  | 3 => schurGlueMid b c
      (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
      (z TriangleCorner.apex)
  | 4 => schurGlueMid b c
      (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
      (z TriangleCorner.rightBase)
  | 5 => schurGlueMid b c
      (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
      (z TriangleCorner.leftBase)

private theorem cr_i0L : sgChildCornerBoundaryIndex 0 TriangleCorner.leftBase = 0 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i0R : sgChildCornerBoundaryIndex 0 TriangleCorner.rightBase = 3 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i0A : sgChildCornerBoundaryIndex 0 TriangleCorner.apex = 4 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i1L : sgChildCornerBoundaryIndex 1 TriangleCorner.leftBase = 3 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i1R : sgChildCornerBoundaryIndex 1 TriangleCorner.rightBase = 1 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i1A : sgChildCornerBoundaryIndex 1 TriangleCorner.apex = 5 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i2L : sgChildCornerBoundaryIndex 2 TriangleCorner.leftBase = 4 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i2R : sgChildCornerBoundaryIndex 2 TriangleCorner.rightBase = 5 := by
  simp [sgChildCornerBoundaryIndex]
private theorem cr_i2A : sgChildCornerBoundaryIndex 2 TriangleCorner.apex = 2 := by
  simp [sgChildCornerBoundaryIndex]

private theorem cr_outerP_left (m : Nat) :
    sgLevelOuterCorner (m + 1) TriangleCorner.leftBase =
      sgChildVertex m 0 (sgLevelOuterCorner m TriangleCorner.leftBase) := by
  apply Subtype.ext
  have h1 : (sgLevelOuterCorner (m + 1) TriangleCorner.leftBase).1 = (0, 0) :=
    sgFaceCornerCoords_all_zero_left (m + 1)
  have h2 : (sgLevelOuterCorner m TriangleCorner.leftBase).1 = (0, 0) :=
    sgFaceCornerCoords_all_zero_left m
  rw [h1]
  change ((0 : ℕ), (0 : ℕ)) =
    sgAddOffset m 0 (sgLevelOuterCorner m TriangleCorner.leftBase).1
  rw [h2]
  simp [sgAddOffset, sgChildOffset]

private theorem cr_outerP_right (m : Nat) :
    sgLevelOuterCorner (m + 1) TriangleCorner.rightBase =
      sgChildVertex m 1 (sgLevelOuterCorner m TriangleCorner.rightBase) := by
  apply Subtype.ext
  have h1 : (sgLevelOuterCorner (m + 1) TriangleCorner.rightBase).1 = (2 ^ (m + 1), 0) :=
    sgFaceCornerCoords_all_one_right (m + 1)
  have h2 : (sgLevelOuterCorner m TriangleCorner.rightBase).1 = (2 ^ m, 0) :=
    sgFaceCornerCoords_all_one_right m
  rw [h1]
  change ((2 : ℕ) ^ (m + 1), (0 : ℕ)) =
    sgAddOffset m 1 (sgLevelOuterCorner m TriangleCorner.rightBase).1
  rw [h2]
  apply Prod.ext
  · simp [sgAddOffset, sgChildOffset, pow_succ, mul_two]
  · simp [sgAddOffset, sgChildOffset]

private theorem cr_outerP_apex (m : Nat) :
    sgLevelOuterCorner (m + 1) TriangleCorner.apex =
      sgChildVertex m 2 (sgLevelOuterCorner m TriangleCorner.apex) := by
  apply Subtype.ext
  have h1 : (sgLevelOuterCorner (m + 1) TriangleCorner.apex).1 = (0, 2 ^ (m + 1)) :=
    sgFaceCornerCoords_all_two_apex (m + 1)
  have h2 : (sgLevelOuterCorner m TriangleCorner.apex).1 = (0, 2 ^ m) :=
    sgFaceCornerCoords_all_two_apex m
  rw [h1]
  change ((0 : ℕ), (2 : ℕ) ^ (m + 1)) =
    sgAddOffset m 2 (sgLevelOuterCorner m TriangleCorner.apex).1
  rw [h2]
  apply Prod.ext
  · simp [sgAddOffset, sgChildOffset]
  · simp [sgAddOffset, sgChildOffset, pow_succ, mul_two]

private theorem cr_bv0 (m : Nat) :
    sgParentBoundaryVertex m 0 = sgLevelOuterCorner (m + 1) TriangleCorner.leftBase := by
  rw [cr_outerP_left]
  have h := sgChildCorner_maps_parentBoundary m 0 TriangleCorner.leftBase
  rw [cr_i0L] at h
  exact h.symm

private theorem cr_bv1 (m : Nat) :
    sgParentBoundaryVertex m 1 = sgLevelOuterCorner (m + 1) TriangleCorner.rightBase := by
  rw [cr_outerP_right]
  have h := sgChildCorner_maps_parentBoundary m 1 TriangleCorner.rightBase
  rw [cr_i1R] at h
  exact h.symm

private theorem cr_bv2 (m : Nat) :
    sgParentBoundaryVertex m 2 = sgLevelOuterCorner (m + 1) TriangleCorner.apex := by
  rw [cr_outerP_apex]
  have h := sgChildCorner_maps_parentBoundary m 2 TriangleCorner.apex
  rw [cr_i2A] at h
  exact h.symm

private theorem cr_e3 (m : Nat) : sgParentBoundaryVertex m 3 = sgParentMidpoint01 m := by
  simp [sgParentBoundaryVertex]
private theorem cr_e4 (m : Nat) : sgParentBoundaryVertex m 4 = sgParentMidpoint02 m := by
  simp [sgParentBoundaryVertex]
private theorem cr_e5 (m : Nat) : sgParentBoundaryVertex m 5 = sgParentMidpoint12 m := by
  simp [sgParentBoundaryVertex]

private theorem cr_interior_row (m : Nat) (lam : ℝ) (X : Fin 3 → SGVertex m → ℝ)
    (hXrow : ∀ k (a : SGVertex m), (∀ c, a ≠ sgLevelOuterCorner m c) →
      sgShiftedRow m lam (X k) a = 0)
    (x : SGVertex (m + 1) → ℝ) (hx : ∀ i a, x (sgChildVertex m i a) = X i a)
    (v : SGVertex (m + 1)) (hv : v ∈ sgParentInteriorSet m) :
    sgShiftedRow (m + 1) lam x v = 0 := by
  classical
  have hfx : ∀ k, (fun w => x (sgChildVertex m k w)) = X k := fun k => funext (hx k)
  rw [← sgChildInteriorSet_union] at hv
  have key : ∀ k : Fin 3, v ∈ sgChildInteriorSet m k → sgShiftedRow (m + 1) lam x v = 0 := by
    intro k hk
    have hkset : v ∈ sgChildVertexSet m k := (Finset.mem_sdiff.mp hk).1
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hkset
    subst ha
    have hother : ∀ t : Fin 3, t ≠ k → sgChildVertex m k a ∉ sgChildVertexSet m t :=
      fun t ht => sgChildInteriorSet_not_mem_other_child m (Ne.symm ht) hk
    rw [sgShiftedRow_child_of_notMemOthers m lam k a hother x, hfx k]
    apply hXrow k a
    intro c hac
    have hnb : sgChildVertex m k a ∉ sgParentBoundarySet m := (Finset.mem_sdiff.mp hk).2
    apply hnb
    rw [hac, sgChildCorner_maps_parentBoundary]
    change _ ∈ Finset.univ.image (sgParentBoundaryVertex m)
    exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
  rcases Finset.mem_union.mp hv with h01 | h2
  · rcases Finset.mem_union.mp h01 with h0 | h1
    · exact key 0 h0
    · exact key 1 h1
  · exact key 2 h2

private theorem cr_succ_aux (m : Nat) (lam a b c : ℝ)
    (h : SgCornerResponse m lam a b)
    (hcdef : 2 * a + lam - b = c) (hc : c ≠ 0) (hc3 : c + 3 * b ≠ 0) :
    SgCornerResponse (m + 1) lam (schurNextDiagonal a b c) (schurNextOffDiagonal b c) := by
  classical
  intro z
  have hc' : c + b = 2 * a + lam := by linarith
  have hx0 : ∀ k : Fin 3, ∃ X : SGVertex m → ℝ,
      (∀ cr, X (sgLevelOuterCorner m cr) =
        crData b c z (sgChildCornerBoundaryIndex k cr)) ∧
      (∀ v : SGVertex m, (∀ cr, v ≠ sgLevelOuterCorner m cr) →
        sgShiftedRow m lam X v = 0) ∧
      (∀ cr, sgShiftedRow m lam X (sgLevelOuterCorner m cr) =
        a * crData b c z (sgChildCornerBoundaryIndex k cr) +
        b * (crData b c z (sgChildCornerBoundaryIndex k TriangleCorner.leftBase) +
          crData b c z (sgChildCornerBoundaryIndex k TriangleCorner.rightBase) +
          crData b c z (sgChildCornerBoundaryIndex k TriangleCorner.apex) -
          crData b c z (sgChildCornerBoundaryIndex k cr))) := by
    intro k
    obtain ⟨X, h1, h2, h3⟩ :=
      h (fun cr => crData b c z (sgChildCornerBoundaryIndex k cr))
    refine ⟨X, h1, h2, ?_⟩
    intro cr
    have := h3 cr
    simp only [sum_triangleCorner] at this
    exact this
  choose X hX1 hX2 hX3 using hx0
  have hcons : ∀ (i : Fin 3) (a' : SGVertex m) (j : Fin 3) (b' : SGVertex m),
      sgChildVertex m i a' = sgChildVertex m j b' → X i a' = X j b' := by
    intro i a' j b' hij
    rcases sgChildVertex_eq_cases m i j a' b' hij with ⟨rfl, rfl⟩ | ⟨cr, cr', ha, hb, hidx⟩
    · rfl
    · rw [ha, hb, hX1 i cr, hX1 j cr', hidx]
  obtain ⟨x, hx⟩ := sgGlue_exists m X hcons
  have hfx : ∀ k, (fun w => x (sgChildVertex m k w)) = X k := fun k => funext (hx k)
  have hm01 : x (sgParentMidpoint01 m) = crData b c z 3 := by
    have e : x (sgParentMidpoint01 m) = X 0 (sgLevelOuterCorner m TriangleCorner.rightBase) :=
      hx 0 (sgLevelOuterCorner m TriangleCorner.rightBase)
    rw [e, hX1 0 TriangleCorner.rightBase, cr_i0R]
  have hm02 : x (sgParentMidpoint02 m) = crData b c z 4 := by
    have e : x (sgParentMidpoint02 m) = X 0 (sgLevelOuterCorner m TriangleCorner.apex) :=
      hx 0 (sgLevelOuterCorner m TriangleCorner.apex)
    rw [e, hX1 0 TriangleCorner.apex, cr_i0A]
  have hm12 : x (sgParentMidpoint12 m) = crData b c z 5 := by
    have e : x (sgParentMidpoint12 m) = X 1 (sgLevelOuterCorner m TriangleCorner.apex) :=
      hx 1 (sgLevelOuterCorner m TriangleCorner.apex)
    rw [e, hX1 1 TriangleCorner.apex, cr_i1A]
  refine ⟨x, ?_, ?_, ?_⟩
  · intro cr
    cases cr
    · rw [cr_outerP_left, hx, hX1 0 TriangleCorner.leftBase]
      simp [crData, cr_i0L]
    · rw [cr_outerP_right, hx, hX1 1 TriangleCorner.rightBase]
      simp [crData, cr_i1R]
    · rw [cr_outerP_apex, hx, hX1 2 TriangleCorner.apex]
      simp [crData, cr_i2A]
  · intro v hv
    change sgShiftedRow (m + 1) lam x v = 0
    by_cases hb : v ∈ sgParentBoundarySet m
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hb
      have hi : ∀ i : Fin 6, i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by decide
      rcases hi i with rfl | rfl | rfl | rfl | rfl | rfl
      · exact absurd (cr_bv0 m) (hv TriangleCorner.leftBase)
      · exact absurd (cr_bv1 m) (hv TriangleCorner.rightBase)
      · exact absurd (cr_bv2 m) (hv TriangleCorner.apex)
      · rw [cr_e3 m, sgShiftedRow_midpoint01, hfx 0, hfx 1,
          hX3 0 TriangleCorner.rightBase, hX3 1 TriangleCorner.leftBase, hm01,
          cr_i0L, cr_i0R, cr_i0A, cr_i1L, cr_i1R, cr_i1A]
        have key := schurGlue_midpoint_row b c (z TriangleCorner.leftBase)
          (z TriangleCorner.rightBase) (z TriangleCorner.apex)
          (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
          hc hc3 rfl
        rw [hc'] at key
        simp only [crData]
        linear_combination key
      · rw [cr_e4 m, sgShiftedRow_midpoint02, hfx 0, hfx 2,
          hX3 0 TriangleCorner.apex, hX3 2 TriangleCorner.leftBase, hm02,
          cr_i0L, cr_i0R, cr_i0A, cr_i2L, cr_i2R, cr_i2A]
        have key := schurGlue_midpoint_row b c (z TriangleCorner.leftBase)
          (z TriangleCorner.apex) (z TriangleCorner.rightBase)
          (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
          hc hc3 (by ring)
        rw [hc'] at key
        simp only [crData]
        linear_combination key
      · rw [cr_e5 m, sgShiftedRow_midpoint12, hfx 1, hfx 2,
          hX3 1 TriangleCorner.apex, hX3 2 TriangleCorner.rightBase, hm12,
          cr_i1L, cr_i1R, cr_i1A, cr_i2L, cr_i2R, cr_i2A]
        have key := schurGlue_midpoint_row b c (z TriangleCorner.rightBase)
          (z TriangleCorner.apex) (z TriangleCorner.leftBase)
          (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
          hc hc3 (by ring)
        rw [hc'] at key
        simp only [crData]
        linear_combination key
    · exact cr_interior_row m lam X (fun k a' h' => hX2 k a' h') x hx v
        ((sgParentInteriorSet_mem_iff m v).2 hb)
  · intro cr
    change sgShiftedRow (m + 1) lam x (sgLevelOuterCorner (m + 1) cr) = _
    cases cr
    · rw [cr_outerP_left, sgShiftedRow_outerLeft, hfx 0,
        hX3 0 TriangleCorner.leftBase, sum_triangleCorner, cr_i0L, cr_i0R, cr_i0A]
      have key := schurGlue_corner_response a b c (z TriangleCorner.leftBase)
        (z TriangleCorner.rightBase) (z TriangleCorner.apex)
        (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
        hc hc3 rfl
      simp only [crData]
      linear_combination key
    · rw [cr_outerP_right, sgShiftedRow_outerRight, hfx 1,
        hX3 1 TriangleCorner.rightBase, sum_triangleCorner, cr_i1L, cr_i1R, cr_i1A]
      have key := schurGlue_corner_response a b c (z TriangleCorner.rightBase)
        (z TriangleCorner.leftBase) (z TriangleCorner.apex)
        (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
        hc hc3 (by ring)
      simp only [crData]
      linear_combination key
    · rw [cr_outerP_apex, sgShiftedRow_outerApex, hfx 2,
        hX3 2 TriangleCorner.apex, sum_triangleCorner, cr_i2L, cr_i2R, cr_i2A]
      have key := schurGlue_corner_response a b c (z TriangleCorner.apex)
        (z TriangleCorner.leftBase) (z TriangleCorner.rightBase)
        (z TriangleCorner.leftBase + z TriangleCorner.rightBase + z TriangleCorner.apex)
        hc hc3 (by ring)
      simp only [crData]
      linear_combination key

/-- Induction step: one gluing step. -/
theorem sgCornerResponse_succ (m : Nat) (lam a b : ℝ)
    (h : SgCornerResponse m lam a b)
    (hc : 2 * a + lam - b ≠ 0) (hc3 : 2 * a + lam - b + 3 * b ≠ 0) :
    SgCornerResponse (m + 1) lam
      (schurNextDiagonal a b (2 * a + lam - b))
      (schurNextOffDiagonal b (2 * a + lam - b)) :=
  cr_succ_aux m lam a b (2 * a + lam - b) h rfl hc hc3

end PhiGenesis.SpectralGap
