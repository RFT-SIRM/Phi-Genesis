import Mathlib.Tactic
import PhiGenesis.H10.GasketVertexOrder

namespace PhiGenesis.H10

variable {α : Type*}

/-- The scan does not depend on the fuel once fuel ≥ input length. -/
theorem gasketFirstOccurrencesAux_fuel_irrel [DecidableEq α] :
    ∀ (f1 f2 : Nat) (xs : List α),
      xs.length ≤ f1 → xs.length ≤ f2 →
      gasketFirstOccurrencesAux f1 xs = gasketFirstOccurrencesAux f2 xs := by
  intro f1
  induction f1 with
  | zero =>
      intro f2 xs h1 h2
      have hx : xs = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp h1)
      subst hx
      cases f2 <;> simp [gasketFirstOccurrencesAux]
  | succ f1 ih =>
      intro f2 xs h1 h2
      cases xs with
      | nil => cases f2 <;> simp [gasketFirstOccurrencesAux]
      | cons a xs =>
          cases f2 with
          | zero => simp at h2
          | succ f2 =>
              simp only [List.length_cons] at h1 h2
              simp only [gasketFirstOccurrencesAux]
              congr 1
              apply ih
              · exact le_trans (List.length_filter_le _ _) (by omega)
              · exact le_trans (List.length_filter_le _ _) (by omega)

/-- If the head block is duplicate-free, it is kept verbatim and the scan
continues on the rest with the head block's elements removed. -/
theorem gasketFirstOccurrences_append_of_nodup [DecidableEq α] :
    ∀ (xs ys : List α), xs.Nodup →
      gasketFirstOccurrences (xs ++ ys) =
        xs ++ gasketFirstOccurrences (ys.filter (fun y => y ∉ xs)) := by
  intro xs
  induction xs with
  | nil =>
      intro ys _
      have h : ys.filter (fun y => y ∉ ([] : List α)) = ys :=
        List.filter_eq_self.mpr (by intro x _; simp)
      simp only [List.nil_append]
      rw [h]
  | cons a xs ih =>
      intro ys hnodup
      rcases List.nodup_cons.mp hnodup with ⟨haNot, hxs⟩
      have hxsFilter : xs.filter (fun x => x ≠ a) = xs := by
        apply List.filter_eq_self.mpr
        intro x hx
        have hxa : x ≠ a := fun hEq => haNot (hEq ▸ hx)
        simp [hxa]
      have hfilt :
          (xs ++ ys).filter (fun x => x ≠ a) =
            xs ++ ys.filter (fun x => x ≠ a) := by
        rw [List.filter_append, hxsFilter]
      have hfy :
          (ys.filter (fun x => x ≠ a)).filter (fun y => y ∉ xs) =
            ys.filter (fun y => y ∉ a :: xs) := by
        rw [List.filter_filter]
        apply List.filter_congr
        intro y _
        by_cases h1 : y = a <;> by_cases h2 : y ∈ xs <;> simp [h1, h2]
      have hlen :
          (xs ++ ys.filter (fun x => x ≠ a)).length ≤ (xs ++ ys).length := by
        simp only [List.length_append]
        have := List.length_filter_le (fun x => decide (x ≠ a)) ys
        omega
      have hstep :
          gasketFirstOccurrences ((a :: xs) ++ ys) =
            a :: gasketFirstOccurrences (xs ++ ys.filter (fun x => x ≠ a)) := by
        have hl : ((a :: xs) ++ ys).length = (xs ++ ys).length + 1 := by
          simp only [List.cons_append, List.length_cons]
        unfold gasketFirstOccurrences
        rw [hl]
        show a :: gasketFirstOccurrencesAux (xs ++ ys).length
            ((xs ++ ys).filter (fun x => x ≠ a)) = _
        rw [hfilt]
        congr 1
        exact gasketFirstOccurrencesAux_fuel_irrel _ _ _ hlen (Nat.le_refl _)
      rw [hstep, ih _ hxs, hfy]
      all_goals rfl

/-- The parent vertex list is the child-0 block followed by the scan of the
remaining children with child-0 vertices removed. -/
theorem gasketVertexOrder_succ_eq_child0_append (n : Nat) :
    gasketVertexOrder (n + 1) =
      (gasketVertexOrder n).map (gasketChildPoint n .corner0) ++
        gasketFirstOccurrences
          (((gasketVertexOrder n).map (gasketChildPoint n .corner1) ++
            (gasketVertexOrder n).map (gasketChildPoint n .corner2)).filter
              (fun y => y ∉ (gasketVertexOrder n).map
                (gasketChildPoint n .corner0))) := by
  have h := gasketFirstOccurrences_append_of_nodup
    ((gasketVertexOrder n).map (gasketChildPoint n .corner0))
    ((gasketVertexOrder n).map (gasketChildPoint n .corner1) ++
      (gasketVertexOrder n).map (gasketChildPoint n .corner2))
    ((gasketVertexOrder_nodup n).map
      (gasketChildPoint_injective n .corner0))
  change
    gasketFirstOccurrences
      ((gasketVertexOrder n).map (gasketChildPoint n .corner0) ++
        ((gasketVertexOrder n).map (gasketChildPoint n .corner1) ++
          (gasketVertexOrder n).map (gasketChildPoint n .corner2))) = _
  convert h

end PhiGenesis.H10
