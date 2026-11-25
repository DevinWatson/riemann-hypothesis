module

public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceFoundations.IsHWSmooth
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightUniqueness.UnitaryOfBlockWMem

@[expose] public section

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding

open Formalism.QuantumDeterminants

variable {k r : ℕ}

def bl (k r : ℕ) (i : Fin (2 * r + k + 1)) : Prop := r ≤ i.val ∧ i.val < r + k

instance (i : Fin (2 * r + k + 1)) : Decidable (bl k r i) := by unfold bl; infer_instance

def eB (k r : ℕ) (q : Fin k) : Fin (2 * r + k + 1) := ⟨r + q.val, by omega⟩

private theorem eB_val_eq_add (q : Fin k) : (eB k r q).val = r + q.val := rfl

theorem ex_eB {i : Fin (2 * r + k + 1)} (hi : bl k r i) : ∃ q, i = eB k r q := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  refine ⟨⟨i.val - r, by omega⟩, Fin.ext ?_⟩
  rw [eB_val_eq_add]
  show i.val = r + (i.val - r)
  omega

theorem sumB (f : Fin (2 * r + k + 1) → ℂ) (hf : ∀ p, ¬ bl k r p → f p = 0) :
    ∑ p, f p = ∑ q : Fin k, f (eB k r q) := by
  rw [← Finset.sum_image (s := Finset.univ) (g := eB k r) (by intro a _ b _ hab; exact PI.HwUniqW.blockIndex_injective hab)]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  apply hf
  intro hb
  obtain ⟨q, rfl⟩ := ex_eB hb
  exact hp (Finset.mem_image_of_mem _ (Finset.mem_univ _))

theorem bw_col (h : Matrix (Fin k) (Fin k) ℂ) (i : Fin (2 * r + k + 1)) {j : Fin (2 * r + k + 1)}
    (hj : ¬ bl k r j) : Formalism.MainNotions.S.blockW k r h i j = if i = j then 1 else 0 := by
  have hj' : ¬ (r ≤ j.val ∧ j.val < r + k) := hj
  by_cases hi : r ≤ i.val ∧ i.val < r + k
  · have hne : i ≠ j := by
      intro e
      subst e
      exact hj' hi
    simp only [Formalism.MainNotions.S.blockW, dif_pos hi, dif_neg hj', if_neg hne]
  · simp only [Formalism.MainNotions.S.blockW, dif_neg hi]

theorem bw_off (h : Matrix (Fin k) (Fin k) ℂ) {i j : Fin (2 * r + k + 1)}
    (hi : ¬ bl k r i) (hj : bl k r j) : Formalism.MainNotions.S.blockW k r h i j = 0 := by
  have hi' : ¬ (r ≤ i.val ∧ i.val < r + k) := hi
  have hne : i ≠ j := by
    intro e
    subst e
    exact hi hj
  simp only [Formalism.MainNotions.S.blockW, dif_neg hi', if_neg hne]

theorem blockW_mul (a b : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r (a * b) = Formalism.MainNotions.S.blockW k r a * Formalism.MainNotions.S.blockW k r b := by
  change PI.UpqRep.blockW k r (a * b) = PI.UpqRep.blockW k r a * PI.UpqRep.blockW k r b
  ext i j
  rw [Matrix.mul_apply]
  by_cases hi : bl k r i
  · by_cases hj : bl k r j
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      have hbl : ∀ q, eB k r q = PI.HwUniqW.bl k r q := fun _ => rfl
      simp only [hbl]
      rw [PI.HwUniqW.blockW_bl, Matrix.mul_apply,
        sumB (fun p => PI.UpqRep.blockW k r a (PI.HwUniqW.bl k r qi) p * PI.UpqRep.blockW k r b p (PI.HwUniqW.bl k r qj))
          (fun p hp => by rw [PI.HwUniqW.blockW_in_out a (PI.HwUniqW.inB_bl qi) hp, zero_mul])]
      simp only [hbl, PI.HwUniqW.blockW_bl]
    · simp only [fun l => show PI.UpqRep.blockW k r b l j = if l = j then 1 else 0 from bw_col b l hj,
        mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte,
        PI.HwUniqW.blockW_in_out a hi hj, PI.HwUniqW.blockW_in_out (a * b) hi hj]
  · rw [PI.HwUniqW.blockW_out _ hi]
    simp only [fun l => PI.HwUniqW.blockW_out a hi (j := l), ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte, PI.HwUniqW.blockW_out b hi]

theorem blockW_one : Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) = 1 := by
  ext i j
  rw [Matrix.one_apply]
  by_cases hi : bl k r i
  · by_cases hj : bl k r j
    · obtain ⟨qi, rfl⟩ := ex_eB hi
      obtain ⟨qj, rfl⟩ := ex_eB hj
      rw [show Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) (eB k r qi) (eB k r qj) =
            (1 : Matrix (Fin k) (Fin k) ℂ) qi qj from PI.HwUniqW.blockW_bl 1 qi qj,
        Matrix.one_apply]
      simp only [show (eB k r qi = eB k r qj) = (qi = qj) from propext PI.HwUniqW.blockIndex_injective.eq_iff]
    · have hne : i ≠ j := by
        intro e
        subst e
        exact hj hi
      rw [show Formalism.MainNotions.S.blockW k r (1 : Matrix (Fin k) (Fin k) ℂ) i j = 0 from
          PI.HwUniqW.blockW_in_out _ hi hj, if_neg hne]
  · exact PI.HwUniqW.blockW_out _ hi

theorem H_blrow {i : Fin (2 * r + k + 1)} (hi : bl k r i) (j : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have hi' : r ≤ i.val ∧ i.val < r + k := hi
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_blcol {j : Fin (2 * r + k + 1)} (hj : bl k r j) (i : Fin (2 * r + k + 1)) :
    Hpk k r i j = if i = j then 1 else 0 := by
  have hj' : r ≤ j.val ∧ j.val < r + k := hj
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_lo {c : Fin (2 * r + k + 1)} (hc : c.val < r) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_hi {c : Fin (2 * r + k + 1)} (hc : r + k < c.val) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c.val + b.val = 2 * r + k then 1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem H_mid {c : Fin (2 * r + k + 1)} (hc : c.val = r + k) (b : Fin (2 * r + k + 1)) :
    Hpk k r c b = if c = b then -1 else 0 := by
  have := b.isLt
  simp only [Formalism.QuantumDeterminants.Hpk, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem bw_mulVec {c : Fin (2 * r + k + 1)} (hc : ¬ bl k r c) (h : Matrix (Fin k) (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h *ᵥ bvec c = bvec c := by
  funext i
  simp only [Formalism.QuantumDeterminants.bvec, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  exact bw_col h i hc

theorem mem_UW {h : Matrix (Fin k) (Fin k) ℂ} (hu : h ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    Formalism.MainNotions.S.blockW k r h ∈ UWset k r (z0 k r) := by
  have hs : hᴴ * h = 1 := by
    have hs' : star h * h = 1 := by
      first
        | exact Matrix.mem_unitaryGroup_iff'.mp hu
    rwa [Matrix.star_eq_conjTranspose] at hs'
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_setOf_eq]
  refine ⟨?_, fun a => ⟨?_, ?_⟩, ?_⟩
  · show (PI.UpqRep.blockW k r h)ᴴ * PI.UpqRep.Hpk k r * PI.UpqRep.blockW k r h = PI.UpqRep.Hpk k r
    rw [PI.HwUniqW.blockW_conjTranspose, Matrix.mul_assoc, PI.HwUniqW.Hpk_blockW_comm,
      ← Matrix.mul_assoc, PI.HwUniqW.blockW_mul, hs, PI.HwUniqW.blockW_one, Matrix.one_mul]
  · apply bw_mulVec
    have := a.isLt
    show ¬ (r ≤ a.val ∧ a.val < r + k)
    omega
  · apply bw_mulVec
    have := a.isLt
    show ¬ (r ≤ 2 * r + k - a.val ∧ 2 * r + k - a.val < r + k)
    omega
  · show Formalism.MainNotions.S.blockW k r h *ᵥ Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k)) =
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.wI k r (Fin.last k))
    apply bw_mulVec
    show ¬ (r ≤ r + k ∧ r + k < r + k)
    omega

end ReciprocityTheory.ChartRestriction.DS.Lap.Base.StandardBasisEmbedding
