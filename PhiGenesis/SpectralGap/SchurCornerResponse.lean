import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurSlots
import PhiGenesis.SpectralGap.SchurGlueAlgebra
import PhiGenesis.SpectralGap.SchurBridgeLevelZero

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

/-- Induction step: one gluing step. -/
theorem sgCornerResponse_succ (m : Nat) (lam a b : ℝ)
    (h : SgCornerResponse m lam a b)
    (hc : 2 * a + lam - b ≠ 0) (hc3 : 2 * a + lam - b + 3 * b ≠ 0) :
    SgCornerResponse (m + 1) lam
      (schurNextDiagonal a b (2 * a + lam - b))
      (schurNextOffDiagonal b (2 * a + lam - b)) := by
  sorry

end PhiGenesis.SpectralGap
