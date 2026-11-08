import Mathlib.Tactic
import PhiGenesis.SpectralGap.SchurLambdaMin

namespace PhiGenesis.SpectralGap

private theorem sum_mul_smul' {ι : Type*} [Fintype ι] (a b : ι → ℝ) (t : ℝ) :
    ∑ v, a v * (t * b v) = t * ∑ v, a v * b v := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem sgForm_smul_self (m : Nat) (lam t : ℝ) (y : SGVertex m → ℝ) :
    sgSignlessShiftedBilinearForm m lam (fun v => t * y v) (fun v => t * y v) =
      t ^ 2 * sgSignlessShiftedBilinearForm m lam y y := by
  unfold sgSignlessShiftedBilinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have h : ∑ v, (sgSignlessLaplacianMatrix m -
      lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * (t * y v) =
      t * ∑ v, (sgSignlessLaplacianMatrix m -
        lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * y v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [h]
  ring

theorem sgForm_smul_right (m : Nat) (lam t : ℝ) (x y : SGVertex m → ℝ) :
    sgSignlessShiftedBilinearForm m lam x (fun v => t * y v) =
      t * sgSignlessShiftedBilinearForm m lam x y := by
  unfold sgSignlessShiftedBilinearForm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  have h : ∑ v, (sgSignlessLaplacianMatrix m -
      lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * (t * y v) =
      t * ∑ v, (sgSignlessLaplacianMatrix m -
        lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) u v * y v := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [h]
  ring

theorem sgShiftedRow_eq' (m : Nat) (lam : ℝ) (x : SGVertex m → ℝ) (v : SGVertex m) :
    sgShiftedRow m lam x v =
      (∑ w, sgSignlessLaplacianMatrix m v w * x w) - lam * x v := by
  classical
  unfold sgShiftedRow
  have h : ∀ w, (sgSignlessLaplacianMatrix m -
      lam • (1 : Matrix (SGVertex m) (SGVertex m) ℝ)) v w * x w =
      sgSignlessLaplacianMatrix m v w * x w -
        (if v = w then lam * x w else 0) := by
    intro w
    by_cases hw : v = w
    · subst hw
      simp [Matrix.sub_apply, Matrix.one_apply]
      ring
    · simp [Matrix.sub_apply, Matrix.one_apply, hw]
  rw [Finset.sum_congr rfl (fun w _ => h w), Finset.sum_sub_distrib,
    Finset.sum_ite_eq]
  simp

/-- A nonnegative form that vanishes at `x` has `x` in its kernel. -/
theorem sgForm_zero_kernel (m : Nat) (lam : ℝ) (x : SGVertex m → ℝ)
    (hnn : ∀ y : SGVertex m → ℝ, 0 ≤ sgSignlessShiftedBilinearForm m lam y y)
    (hx : sgSignlessShiftedBilinearForm m lam x x = 0) :
    ∀ u, sgShiftedRow m lam x u = 0 := by
  classical
  intro u
  let y : SGVertex m → ℝ := fun v => if v = u then 1 else 0
  have hG : sgSignlessShiftedBilinearForm m lam x y = sgShiftedRow m lam x u := by
    rw [sgForm_cross_eq]
    simp [y]
  set G := sgSignlessShiftedBilinearForm m lam x y with hGdef
  set F := sgSignlessShiftedBilinearForm m lam y y with hFdef
  have hF : 0 ≤ F := hnn y
  have key : ∀ t : ℝ, 0 ≤ t ^ 2 * F + 2 * (t * G) := by
    intro t
    have h1 := hnn (fun v => x v + t * y v)
    have hpol := sgSignlessShiftedBilinearForm_polarization m lam x (fun v => t * y v)
    beta_reduce at hpol
    rw [hpol, hx, sgForm_smul_self, sgForm_smul_right] at h1
    nlinarith [h1]
  have hF1 : 0 < F + 1 := by linarith
  set t : ℝ := -G / (F + 1) with ht
  have htG : G = -t * (F + 1) := by
    rw [ht]
    field_simp
  have hk := key t
  have e : 2 * (t * G) = -2 * t ^ 2 * (F + 1) := by
    rw [htG]
    ring
  have hsq : t ^ 2 * (F + 2) ≤ 0 := by nlinarith [hk, e]
  have h2 : t ^ 2 ≤ 0 := by nlinarith [sq_nonneg t, hF, hsq, mul_nonneg (sq_nonneg t) hF]
  have ht0 : t = 0 := by
    by_contra hne
    have := sq_pos_of_ne_zero hne
    linarith
  have hG0 : G = 0 := by
    rw [htG, ht0]
    ring
  rw [← hG]
  exact hG0

/-- The set of eigenvalues of the level-`m` signless Laplacian. -/
def sgEigenSet (m : Nat) : Set ℝ :=
  {μ | ∃ v : SGVertex m → ℝ, (∃ u, v u ≠ 0) ∧
    ∀ u, ∑ w, sgSignlessLaplacianMatrix m u w * v w = μ * v u}

/-- At an A1 root in the window: the root is an eigenvalue, and no eigenvalue is smaller. -/
theorem sgBottomEigenvalue_atRoot (n : ℕ) (r : ℝ)
    (hr : r ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper)
    (hroot : schurBootstrapA1AtLevel r n = 0) :
    r ∈ sgEigenSet (6 + n) ∧ ∀ μ ∈ sgEigenSet (6 + n), r ≤ μ := by
  classical
  obtain ⟨hnn, x, hxpos, hx0⟩ := sgRayleighAtRoot n r hr hroot
  constructor
  · refine ⟨x, ?_, ?_⟩
    · by_contra h
      push_neg at h
      have hz : ∑ v, (x v) ^ 2 = 0 :=
        Finset.sum_eq_zero (fun v _ => by rw [h v]; norm_num)
      linarith
    · intro u
      have h := sgForm_zero_kernel (6 + n) r x hnn hx0 u
      rw [sgShiftedRow_eq'] at h
      linarith
  · rintro μ ⟨v, ⟨u0, hu0⟩, hev⟩
    have hform := hnn v
    rw [sgShiftedForm_eq_rowSum] at hform
    have hexp : ∑ u, v u * sgShiftedRow (6 + n) r v u =
        (μ - r) * ∑ u, (v u) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u _
      rw [sgShiftedRow_eq', hev u]
      ring
    have hpos : 0 < ∑ u, (v u) ^ 2 := by
      have h1 : 0 < (v u0) ^ 2 := sq_pos_of_ne_zero hu0
      have h2 : (v u0) ^ 2 ≤ ∑ u, (v u) ^ 2 :=
        Finset.single_le_sum (f := fun u => (v u) ^ 2)
          (fun u _ => sq_nonneg (v u)) (Finset.mem_univ u0)
      linarith
    rw [hexp] at hform
    by_contra hlt
    push_neg at hlt
    nlinarith [mul_pos (sub_pos.2 hlt) hpos]

/-- The canonical A1 root of level `6 + n` is the least eigenvalue of `Q_{6+n}`. -/
theorem sgChosenRoot_isLeast (n : ℕ) :
    IsLeast (sgEigenSet (6 + n)) (schurBootstrapA1AtLevel_chosenRoot n) := by
  obtain ⟨hmem, hz⟩ := schurBootstrapA1AtLevel_chosenRoot_spec n
  obtain ⟨h1, h2⟩ := sgBottomEigenvalue_atRoot n _ hmem hz
  exact ⟨h1, fun μ hμ => h2 μ hμ⟩

/-- The least eigenvalues of the signless Laplacians `Q_{6+n}` converge to a point of the window. -/
theorem sgLeastEigenvalue_converges :
    ∃ ℓ : ℝ, ℓ ∈ Set.Icc schurBootstrapLambdaLower schurBootstrapLambdaUpper ∧
      ∃ a : ℕ → ℝ, (∀ n, IsLeast (sgEigenSet (6 + n)) (a n)) ∧
        Filter.Tendsto a Filter.atTop (nhds ℓ) :=
  ⟨schurBootstrapA1AtLevel_rootLimit, schurBootstrapA1AtLevel_rootLimit_mem,
    schurBootstrapA1AtLevel_chosenRoot, sgChosenRoot_isLeast,
    schurBootstrapA1AtLevel_chosenRoot_tendsto⟩

end PhiGenesis.SpectralGap
