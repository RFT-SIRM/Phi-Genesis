import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurEigenvalue

namespace PhiGenesis.SpectralGap

/-- Eigenvalues of the signed local-face matrix, in the usual sense. -/
def sgSignedEigenSet (m : Nat) : Set ℝ :=
  {μ | ∃ v : SGVertex m → ℝ, (∃ u, v u ≠ 0) ∧
    ∀ u, ∑ w, sgSignedLaplacianMatrix m u w * v w = μ * v u}

private theorem gauge_ne_zero (m : Nat) (u : SGVertex m) : sgVertexGauge u ≠ 0 := by
  intro h
  have := sgVertexGauge_sq u
  rw [h] at this
  norm_num at this

private theorem signed_entry (m : Nat) (u w : SGVertex m) :
    sgSignedLaplacianMatrix m u w =
      sgVertexGauge u * sgSignlessLaplacianMatrix m u w * sgVertexGauge w := by
  rw [sgSignedLaplacianMatrix_eq_gauge_conj m]
  simp [Matrix.mul_diagonal, Matrix.diagonal_mul]

/-- The signed matrix and the signless matrix have the same eigenvalues. -/
theorem sgSignedEigenSet_eq (m : Nat) : sgSignedEigenSet m = sgEigenSet m := by
  ext μ
  constructor
  · rintro ⟨v, ⟨u0, hu0⟩, hev⟩
    refine ⟨fun u => sgVertexGauge u * v u,
      ⟨u0, mul_ne_zero (gauge_ne_zero m u0) hu0⟩, ?_⟩
    intro u
    have h1 : sgVertexGauge u *
        ∑ w, sgSignlessLaplacianMatrix m u w * (sgVertexGauge w * v w) = μ * v u := by
      rw [← hev u]
      simp_rw [signed_entry]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      ring
    have hg := sgVertexGauge_sq u
    calc ∑ w, sgSignlessLaplacianMatrix m u w * (sgVertexGauge w * v w)
        = sgVertexGauge u * (sgVertexGauge u *
            ∑ w, sgSignlessLaplacianMatrix m u w * (sgVertexGauge w * v w)) := by
          rw [← mul_assoc, ← pow_two, hg, one_mul]
      _ = μ * (sgVertexGauge u * v u) := by rw [h1]; ring
  · rintro ⟨v, ⟨u0, hu0⟩, hev⟩
    refine ⟨fun u => sgVertexGauge u * v u,
      ⟨u0, mul_ne_zero (gauge_ne_zero m u0) hu0⟩, ?_⟩
    intro u
    have h : ∑ w, sgSignedLaplacianMatrix m u w * (sgVertexGauge w * v w) =
        sgVertexGauge u * ∑ w, sgSignlessLaplacianMatrix m u w * v w := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro w _
      rw [signed_entry]
      linear_combination
        (sgVertexGauge u * sgSignlessLaplacianMatrix m u w * v w) * sgVertexGauge_sq w
    rw [h, hev u]
    ring

/-- The least eigenvalues of the signed matrices on levels `6 + n` converge into the window. -/
theorem sgSignedLeastEigenvalue_converges :
    ∃ ℓ : ℝ, ℓ ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper ∧
      ∃ a : ℕ → ℝ, (∀ n, IsLeast (sgSignedEigenSet (6 + n)) (a n)) ∧
        Filter.Tendsto a Filter.atTop (nhds ℓ) := by
  obtain ⟨ℓ, hℓ, a, ha, ht⟩ := sgLeastEigenvalue_converges
  exact ⟨ℓ, hℓ, a, fun n => by rw [sgSignedEigenSet_eq]; exact ha n, ht⟩

end PhiGenesis.SpectralGap
