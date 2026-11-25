module

public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.SmoothDefs
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.HidaSetting
import Mathlib.Tactic.TypeStar
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.Decomp
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.TensorRepresentations.TraceFormula
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Basic.Complex.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Algebra.Polynomial.Eval.Degree
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.DataGenSubIrred

section
@[expose] public section

noncomputable section

open Finset Polynomial

namespace ReciprocityTheory.ChartRestriction.DS

theorem moment_poly {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (Q : ℂ[X]) :
    ∑ i, u i * Q.eval (b i) = ∑ s, r s * Q.eval (a s) := by
  simp only [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ i, u i * (Q.coeff k * b i ^ k) = Q.coeff k * ∑ i, u i * b i ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = Q.coeff k * ∑ s, r s * a s ^ k := by rw [h k]
    _ = ∑ s, r s * (Q.coeff k * a s ^ k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

theorem moment_fibre {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (p : ℂ) :
    ∑ i ∈ univ.filter (fun i => b i = p), u i = ∑ s ∈ univ.filter (fun s => a s = p), r s := by
  classical
  set S : Finset ℂ := (univ.image b ∪ univ.image a).erase p with hS
  have hne : (∏ s ∈ S, (p - s)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun s hs => sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  let Q : ℂ[X] := C (∏ s ∈ S, (p - s))⁻¹ * ∏ s ∈ S, (X - C s)
  have hQ : ∀ x, x ∈ univ.image b ∪ univ.image a → Q.eval x = if x = p then 1 else 0 := by
    intro x hx
    simp only [Q, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with hxp
    · subst hxp
      exact inv_mul_cancel₀ hne
    · rw [Finset.prod_eq_zero (i := x) (Finset.mem_erase.mpr ⟨hxp, hx⟩) (sub_self x), mul_zero]
  have e := moment_poly b u a r h Q
  rw [Finset.sum_filter, Finset.sum_filter]
  calc ∑ i, (if b i = p then u i else 0) = ∑ i, u i * Q.eval (b i) :=
        Finset.sum_congr rfl fun i _ => by
          rw [hQ (b i) (Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp
    _ = ∑ s, r s * Q.eval (a s) := e
    _ = _ := Finset.sum_congr rfl fun s _ => by
          rw [hQ (a s) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ _)))]
          split_ifs <;> simp

variable {n : ℕ}

end ReciprocityTheory.ChartRestriction.DS
end
end
end

section
@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section Helpers
variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem tpsc_single_mem {S : Submodule ℂ M} {x : M} (hx : x ∈ S) (c : Fin n) :
    (Pi.single c x : Fin n → M) ∈ tensSub S := by
  refine Submodule.mem_pi.2 fun d _ => ?_
  by_cases h : d = c
  · subst h; simpa using hx
  · simp [h]

theorem tpsc_coord_mem {S : Submodule ℂ M} {f : Fin n → M} (hf : f ∈ tensSub S) (c : Fin n) : f c ∈ S :=
  Submodule.mem_pi.1 hf c (Set.mem_univ _)

theorem tpsc_tensV_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensV E a b (Pi.single c x) = Pi.single c (E a b x) + if b = c then Pi.single a x else 0 := by
  funext d
  rw [tensV_coord]
  by_cases hdc : d = c <;> by_cases hda : d = a <;> by_cases hbc : b = c <;>
    simp [Pi.single_apply, hdc, hda, hbc] <;> split_ifs <;> simp_all

theorem tpsc_tensVd_single (E : Fin n → Fin n → Module.End ℂ M) (a b c : Fin n) (x : M) :
    tensVd E a b (Pi.single c x) = Pi.single c (E a b x) - if a = c then Pi.single b x else 0 := by
  funext d
  rw [tensVd_coord]
  by_cases hdc : d = c <;> by_cases hdb : d = b <;> by_cases hac : a = c <;>
    simp [Pi.single_apply, hdc, hdb, hac] <;> split_ifs <;> simp_all

end Helpers

def tpscK (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (c d : Fin n) : ℂ := cond dual (star (k c d)) (k c d)

theorem tpscK_rows {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (c c' : Fin n) : ∑ d, tpscK dual k c' d * star (tpscK dual k c d) = if c' = c then 1 else 0 := by
  have hu : k * star k = 1 := Matrix.mem_unitaryGroup_iff.1 hk
  cases dual
  · have := congrFun (congrFun hu c') c
    simpa [tpscK, Matrix.mul_apply, Matrix.one_apply] using this
  · have := congrFun (congrFun hu c) c'
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [show (∑ d, star (k c' d) * k c d) = ∑ d, k c d * star (k c' d) from
      Finset.sum_congr rfl fun d _ => mul_comm _ _, this]
    by_cases h : c' = c
    · subst h; simp
    · simp [h, Ne.symm h]

theorem tpscK_cols {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Matrix.unitaryGroup (Fin n) ℂ) (dual : Bool)
    (e d : Fin n) : ∑ c, tpscK dual k c d * star (tpscK dual k c e) = if e = d then 1 else 0 := by
  have hu : star k * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk
  cases dual
  · have := congrFun (congrFun hu e) d
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_false]
    rw [show (∑ c, k c d * star (k c e)) = ∑ c, star (k c e) * k c d from
      Finset.sum_congr rfl fun c _ => mul_comm _ _, this]
  · have := congrFun (congrFun hu d) e
    simp only [Matrix.mul_apply, Matrix.one_apply, Matrix.star_apply] at this
    simp only [tpscK, cond_true, star_star]
    rw [this]
    by_cases h : e = d
    · subst h; simp
    · simp [h, Ne.symm h]

section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {ε : Fin n → Bool}
  {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
  {V : Submodule ℂ D} {A : Module.End ℂ (Fin n → D)}

theorem ptr_mem {dual : Bool} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ x ∈ genSub E V, ptr A x ∈ genSub E V := by
  intro x hx
  rw [ptr_apply]
  exact Submodule.sum_mem _ fun c _ => tpsc_coord_mem (hA.1 _ (tpsc_single_mem hx c)) c

theorem ptr_comm {dual : Bool} (hE : IsGlRep E) (hA : IsGKEndo dual ε σ E (genSub E V) A) (a b : Fin n) :
    ∀ x ∈ genSub E V, ptr A (E a b x) = E a b (ptr A x) := by
  intro x hx
  have hs : ∀ c, (Pi.single c x : Fin n → D) ∈ tensSub (genSub E V) := fun c => tpsc_single_mem hx c

  rw [ptr_apply, ptr_apply, map_sum]
  cases dual
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) +
        (if c = a then A (Pi.single c x) b else 0) - (if b = c then A (Pi.single a x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensV E a b (Pi.single c x) - (if b = c then Pi.single a x else 0) := by
        rw [tpsc_tensV_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_false] at h2
      rw [h1, map_sub, h2, Pi.sub_apply, tensV_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, add_sub_cancel_right]
  · have key : ∀ c, A (Pi.single c (E a b x)) c = E a b (A (Pi.single c x) c) -
        (if c = b then A (Pi.single c x) a else 0) + (if a = c then A (Pi.single b x) c else 0) := by
      intro c
      have h1 : (Pi.single c (E a b x) : Fin n → D) =
          tensVd E a b (Pi.single c x) + (if a = c then Pi.single b x else 0) := by
        rw [tpsc_tensVd_single]; abel
      have h2 := hA.2.1 a b _ (hs c)
      simp only [tensF, cond_true] at h2
      rw [h1, map_add (f := _), h2, Pi.add_apply, tensVd_coord]
      split_ifs <;> simp
    simp only [key, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, sub_add_cancel]

theorem tpsc_kDiag (dual : Bool) (k : Matrix (Fin n) (Fin n) ℂ) (f : Fin n → H) (c : Fin n) :
    kDiag dual σ k f c = ∑ d, tpscK dual k c d • σ k (f d) := rfl

theorem ptr_kcomm {dual : Bool} (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∀ k ∈ Kset ε, ∀ x ∈ genSub E V, ∀ y ∈ genSub E V, (y : H) = σ k (x : H) →
      ((ptr A y : D) : H) = σ k ((ptr A x : D) : H) := by
  intro k hk x hx y hy hxy
  have hku := hk.1
  let g : Fin n → Fin n → D := fun c d => star (tpscK dual k c d) • x
  have hg : ∀ c, g c ∈ tensSub (genSub E V) := fun c =>
    Submodule.mem_pi.2 fun d _ => Submodule.smul_mem _ _ hx
  have hgs : ∀ c, g c = ∑ e, star (tpscK dual k c e) • (Pi.single e x : Fin n → D) := by
    intro c; funext d
    simp [g, Finset.sum_apply, Pi.single_apply]
  have hf' : ∀ c, (fun c' => (((Pi.single c y : Fin n → D) c' : D) : H)) =
      kDiag dual σ k (fun d => ((g c d : D) : H)) := by
    intro c; funext c'
    rw [tpsc_kDiag]
    simp only [g, Submodule.coe_smul, map_smul, smul_smul]
    rw [← Finset.sum_smul, tpscK_rows hku dual c c', ← hxy]
    by_cases h : c' = c
    · subst h; simp
    · simp [h]
  have hAf : ∀ c c', ((A (Pi.single c y) c' : D) : H) = ∑ d, tpscK dual k c' d •
      σ k (∑ e, star (tpscK dual k c e) • ((A (Pi.single e x) d : D) : H)) := by
    intro c c'
    have := congrFun (hA.2.2 k hk _ (hg c) _ (tpsc_single_mem hy c) (hf' c)) c'
    rw [this, tpsc_kDiag, hgs c]

    simp [map_sum, map_smul, Finset.sum_apply]

  rw [ptr_apply, ptr_apply, Submodule.coe_sum, Submodule.coe_sum, map_sum]

  simp only [hAf, map_sum, map_smul, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, tpscK_cols hku dual]
  simp [ite_smul]

end

theorem ptr_scalar (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) {A : Module.End ℂ (Fin n → D)} (hA : IsGKEndo dual ε σ E (genSub E V) A) :
    ∃ c : ℂ, ∀ x ∈ genSub E V, ptr A x = c • x :=
  data_end_scalar hgap hσ hD hV hc hVK (ptr A) (ptr_mem hA) (fun a b => ptr_comm hD.glRep hA a b)
    (ptr_kcomm hσ hD hA)

end ReciprocityTheory.ChartRestriction.DS
end
end
end

@[expose] public section

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

open MeasureTheory

section Generic

variable {W : Type*} [AddCommGroup W] [Module ℂ W]

theorem pm_pow_eig (A : Module.End ℂ W) {z : ℂ} {f : W} (h : A f = z • f) (k : ℕ) :
    (A ^ k) f = z ^ k • f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_apply_eq_comp, ih, map_smul, h, smul_smul, pow_succ]

theorem pm_proj_decomp (A Q : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ) (z : ℂ)
    (hQ1 : ∀ f ∈ T, A f = z • f → Q f = f) (hQ0 : ∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0)
    (fb : ℝ → W) (hfb : ∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) :
    Q (∑ b ∈ B, fb b) = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then fb b else 0 := by

  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  split_ifs with h
  · exact hQ1 _ (hfb b).1 (by rw [← h]; exact (hfb b).2)
  · exact hQ0 _ (hfb b).1 _ h (hfb b).2

theorem pm_agree (A : Module.End ℂ W) (T : Submodule ℂ W) (B : Finset ℝ)
    (hdec : ∀ f ∈ T, ∃ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b)
    (P : ℝ → Module.End ℂ W)
    (hP1 : ∀ b, ∀ f ∈ T, A f = ((b : ℝ) : ℂ) • f → P b f = f)
    (hP0 : ∀ b, ∀ f ∈ T, ∀ z' : ℂ, z' ≠ ((b : ℝ) : ℂ) → A f = z' • f → P b f = 0) :
    (∀ f ∈ T, ∀ k : ℕ, (A ^ k) f = ∑ b ∈ B, ((b : ℝ) : ℂ) ^ k • P b f) ∧
      ∀ (Q : Module.End ℂ W) (z : ℂ), (∀ f ∈ T, A f = z • f → Q f = f) →
        (∀ f ∈ T, ∀ z' : ℂ, z' ≠ z → A f = z' • f → Q f = 0) →
        ∀ f ∈ T, Q f = ∑ b ∈ B, if ((b : ℝ) : ℂ) = z then P b f else 0 := by
  have hPb : ∀ fb : ℝ → W, (∀ b, fb b ∈ T ∧ A (fb b) = ((b : ℝ) : ℂ) • fb b) →
      ∀ b ∈ B, P b (∑ b' ∈ B, fb b') = fb b := by
    intro fb hfb b hb
    rw [pm_proj_decomp A (P b) T B _ (hP1 b) (hP0 b) fb hfb]
    simp [Complex.ofReal_inj, hb]
  refine ⟨fun f hf k => ?_, fun Q z hQ1 hQ0 f hf => ?_⟩
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf

    rw [map_sum]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb, pm_pow_eig A (hfb b).2]
  · obtain ⟨fb, hfb, rfl⟩ := hdec f hf
    rw [pm_proj_decomp A Q T B z hQ1 hQ0 fb hfb]
    refine Finset.sum_congr rfl fun b hb => ?_
    rw [hPb fb hfb b hb]

end Generic

theorem pm_single_mem {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M) {x : M} (hx : x ∈ S)
    (c : Fin n) : Pi.single c x ∈ tensSub (n := n) S := by
  refine tset_mem.2 fun i => ?_
  by_cases h : i = c <;> simp [h, hx]

theorem pm_ptr {M : Type*} [AddCommGroup M] [Module ℂ M] (S : Submodule ℂ M)
    (Q : Module.End ℂ (Fin n → M)) (R : ℝ → Module.End ℂ (Fin n → M)) (B : Finset ℝ) (g : ℝ → ℂ)
    (hQ : ∀ f ∈ tensSub S, Q f = ∑ b ∈ B, g b • R b f) {x : M} (hx : x ∈ S) :
    ptr Q x = ∑ b ∈ B, g b • ptr (R b) x := by
  simp only [ptr_apply, hQ _ (pm_single_mem S hx _), Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  exact Finset.sum_comm

theorem pm_resid (dual : Bool) (lam : Fin n → ℝ) (s : Fin n) :
    resid (poleF dual lam) s = ((ratioF dual lam s : ℝ) : ℂ) := by
  cases dual
  · exact resid_poleV lam s
  · exact resid_poleVd lam s

theorem pm_pole_inj (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) : Function.Injective (poleF dual lam) := by
  cases dual
  · exact poleV_injective hl.injective
  · exact poleVd_injective hl.injective

theorem pm_char (dual : Bool) {M : Type*} [AddCommGroup M] [Module ℂ M] {E : Fin n → Fin n → Module.End ℂ M}
    {lam : Fin n → ℝ} {S : Submodule ℂ M} (hS : HasGelfandChar E lam S) (k : ℕ) (x : M) (hx : x ∈ S) :
    ptr (eeF dual E ^ k) x = PowerSeries.coeff (k + 1) (resSeries (poleF dual lam)) • x := by
  cases dual
  · exact ptr_eeV_pow_char hS k x hx
  · exact ptr_eeVd_pow_char hS k x hx

theorem pm_core (dual : Bool) {lam : Fin n → ℝ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {ε : Fin n → Bool}
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {D : Submodule ℂ H} {E : Fin n → Fin n → Module.End ℂ D}
    (hσ : IsURepOn (UJset ε) σ) (hD : IsDerivedOn ε σ D E) (hsm : ∀ v : D, IsSmoothVecU ε σ v)
    {V : Submodule ℂ D} (hgap : StdGap ε lam) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hc : ∀ v ∈ V, casimir E v = (casVal lam : ℂ) • v)
    (hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v) (hW : ∀ v ∈ genSub E V, ∀ w ∈ genSub E V, MemLp (fun g : Formalism.REAL.UJ ε =>
      ((Real.sqrt (S7.hs (Formalism.MainNotions.S.umat g)) : ℝ) : ℂ) * inner ℂ ((w : D) : H) (σ (Formalism.MainNotions.S.umat g) ((v : D) : H)))
      2 (Formalism.REAL.muG ε)) (hG : HasGelfandChar E lam (genSub E V)) :
    ∃ B : Finset ℝ, ∃ c : ℝ → ℂ, ∃ P : ℝ → Module.End ℂ (Fin n → D),
      (∀ z : ℂ, ∀ f ∈ tensSub (genSub E V), f ≠ 0 → eeF dual E f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), P b f ∈ tensSub (genSub E V)) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E (P b f) = ((b : ℝ) : ℂ) • P b f) ∧
      (∀ b, ∀ f ∈ tensSub (genSub E V), eeF dual E f = ((b : ℝ) : ℂ) • f → P b f = f) ∧
      (∀ b, ∀ x ∈ genSub E V, ptr (P b) x = c b • x) ∧
      (∀ b, c b = 0 → ∀ f ∈ tensSub (genSub E V), P b f = 0) ∧
      (∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ), (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
        (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
        ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x) ∧
      (∀ p : ℂ, (∑ b ∈ B, if ((b : ℝ) : ℂ) = p then c b else 0) =
        ∑ s ∈ univ.filter (fun s => poleF dual lam s = p), ((ratioF dual lam s : ℝ) : ℂ)) ∧
      ∃ x₀ ∈ genSub E V, x₀ ≠ 0 := by
  obtain ⟨B, hdec, hev⟩ := ee_decomp dual hσ hD hgap hV hc hVK hW
  have hPex := fun b : ℝ => eigenProj_exists dual hσ hD hgap hV hc hVK hW ((b : ℝ) : ℂ)
  choose P hPG hPP hPz hP1 hP0 using hPex
  have hsc := fun b => ptr_scalar dual hσ hD hgap hV hc hVK (hPG b)
  choose c hcb using hsc
  have hPB := fun b => eigenProj_formB dual hσ hD hgap hV hc hVK hW _ (hPG b).1 (hPz b) (hP1 b) (hP0 b)
  have htr := fun b => trace_nonneg dual hσ hD hsm hgap hV hc hVK hW (hPG b) (hPP b) (hPB b) (hPz b) (hcb b)
  obtain ⟨hpow, hagr⟩ := pm_agree (eeF dual E) (tensSub (genSub E V)) B hdec P hP1 hP0
  have hQ : ∀ (Q : Module.End ℂ (Fin n → D)) (z : ℂ),
      (∀ f ∈ tensSub (genSub E V), eeF dual E f = z • f → Q f = f) →
      (∀ f ∈ tensSub (genSub E V), ∀ z' : ℂ, z' ≠ z → eeF dual E f = z' • f → Q f = 0) →
      ∀ x ∈ genSub E V, ptr Q x = (∑ b ∈ B, if ((b : ℝ) : ℂ) = z then c b else 0) • x := by
    intro Q z hQ1 hQ0 x hx
    rw [pm_ptr (genSub E V) Q P B (fun b => if ((b : ℝ) : ℂ) = z then 1 else 0)
      (fun f hf => by
        rw [hagr Q z hQ1 hQ0 f hf]
        exact sum_congr rfl fun b _ => by split_ifs <;> simp) hx, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x hx]
    split_ifs <;> simp
  have hVle : V ≤ genSub E V := by
    unfold genSub
    exact le_sInf fun T hT => hT.1
  obtain ⟨x₀, hx₀V, hx₀0, -⟩ := hV.2.2.2
  have hx₀ : x₀ ∈ genSub E V := hVle hx₀V
  have hmom : ∀ k : ℕ, ∑ i : B, c i * ((i : ℝ) : ℂ) ^ k =
      ∑ s, resid (poleF dual lam) s * poleF dual lam s ^ k := by
    intro k
    rw [Finset.sum_coe_sort B (fun b => c b * ((b : ℝ) : ℂ) ^ k), ← resSeries_coeff_succ (pm_pole_inj dual hgap.1) k]
    apply smul_left_injective ℂ hx₀0
    beta_reduce
    rw [← pm_char dual hG k x₀ hx₀, pm_ptr (genSub E V) _ P B (fun b => ((b : ℝ) : ℂ) ^ k)
      (fun f hf => hpow f hf k) hx₀, Finset.sum_smul]
    refine sum_congr rfl fun b _ => ?_
    rw [hcb b x₀ hx₀, smul_smul, mul_comm (c b)]
  refine ⟨B, c, P, hev, fun b => (hPG b).1, hPz, hP1, hcb, fun b h0 => (htr b).2.2 h0, hQ, fun p => ?_,
    x₀, hx₀, hx₀0⟩
  have hf := moment_fibre (fun i : B => ((i : ℝ) : ℂ)) (fun i => c i) (poleF dual lam) (resid (poleF dual lam)) hmom p
  rw [Finset.sum_filter, Finset.sum_coe_sort B (fun b => if ((b : ℝ) : ℂ) = p then c b else 0)] at hf
  rw [hf]
  exact sum_congr rfl fun s _ => pm_resid dual lam s

theorem pm_filter_pole (dual : Bool) {lam : Fin n → ℝ} (hl : StrictAnti lam) (s : Fin n) :
    univ.filter (fun s' => poleF dual lam s' = poleF dual lam s) = {s} := by
  ext t
  simp [(pm_pole_inj dual hl).eq_iff]

theorem pm_sum_single {B : Finset ℝ} {b : ℝ} (hb : b ∈ B) (c : ℝ → ℂ) :
    (∑ b' ∈ B, if ((b' : ℝ) : ℂ) = ((b : ℝ) : ℂ) then c b' else 0) = c b := by
  simp [Complex.ofReal_inj, hb]

end ReciprocityTheory.ChartRestriction.DS
