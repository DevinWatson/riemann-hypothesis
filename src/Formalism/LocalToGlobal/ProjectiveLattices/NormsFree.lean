module

public import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public section

noncomputable section

namespace Formalism.L2.PjFree

open Formalism.L2.Pj

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

section Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
  (X : Comp → Data E r) (la : ∀ c, ReciprocityTheory.ChartRestriction.G.FD.Wt (X c).Ψ r)

theorem supE_add_le (P Q : FDSec X) : supE X la (P + Q) ≤ supE X la P + supE X la Q := by
  unfold supE
  refine iSup_le fun p => ?_
  have key : (X p.1).pnorm (la p.1) ((P + Q) p.1) p.2 ≤
      (X p.1).pnorm (la p.1) (P p.1) p.2 + (X p.1).pnorm (la p.1) (Q p.1) p.2 := by
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_add_le _ _)
      (Finset.prod_nonneg fun τ _ => Finset.prod_nonneg fun i _ => Real.rpow_nonneg (norm_nonneg _) _)
  exact ((ENNReal.ofReal_le_ofReal key).trans ENNReal.ofReal_add_le).trans
    (add_le_add (le_iSup_of_le p le_rfl) (le_iSup_of_le p le_rfl))

theorem supE_smul (a : ℂ) (P : FDSec X) : supE X la (a • P) = ENNReal.ofReal ‖a‖ * supE X la P := by
  unfold supE
  rw [ENNReal.mul_iSup]
  refine iSup_congr fun p => ?_
  rw [← ENNReal.ofReal_mul (norm_nonneg a)]
  congr 1
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul]
  ring

theorem supE_ne_top [Fintype Comp] {P : FDSec X} (h : P ∈ holSub X la) : supE X la P ≠ ⊤ := by
  unfold holSub at h
  induction h using Submodule.span_induction with
  | mem P hP =>
    choose C hC using fun c => (hP c).1.2
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := ∑ c, |C c|))
      (iSup_le fun p => ENNReal.ofReal_le_ofReal ?_)
    calc _ ≤ C p.1 := hC p.1 p.2.1 p.2.2
      _ ≤ |C p.1| := le_abs_self _
      _ ≤ ∑ c, |C c| :=
        Finset.single_le_sum (f := fun c => |C c|) (fun c _ => abs_nonneg _) (Finset.mem_univ _)
  | zero =>
    unfold supE
    refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := 0)) (iSup_le fun p => ?_)
    unfold ReciprocityTheory.ChartRestriction.G.FD.Data.pnorm
    simp
  | add P Q _ _ hP hQ =>
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨hP, hQ⟩) (supE_add_le X la P Q)
  | smul a P _ hP =>
    rw [supE_smul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hP

end Sup

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)


open Classical in
def goodOf (σ : c.F →+* ℂ) : c.F →+* ℂ := if GoodEmb c σ then σ else (starRingEnd ℂ).comp σ

theorem goodEmb_goodOf (σ : c.F →+* ℂ) : GoodEmb c (goodOf c σ) :=
  Formalism.L2.Pj.goodEmb_goodOf (c := c) σ

def lieFac (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : ℝ :=
  Real.exp (-((∑ τ : E →+* ℂ, ∑ i : Fin (Dw.mult τ), (a (τ, i) : ℝ)) / 2) * Real.log (2 * Real.pi * x))

theorem lieFac_pos (Dw : Datum H) (x : ℝ) (a : (E →+* ℂ) × ℕ → ℕ) : 0 < lieFac Dw x a := by
  unfold lieFac
  exact Real.exp_pos _

def supC (x : ℝ) (σ : c.F →+* ℂ) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (f : Rul Xo c) : ℝ :=
  lieFac Dw x a * supN (U σ).X (laU (U σ) a n) (rdU (U σ) f)

def SupDef : Prop :=
  ∀ a n, Dom a n → ∀ σ, GoodEmb c σ → ∀ f ∈ cusp Xo c U a n, supN (U σ).X (laU (U σ) a n) (rdU (U σ) f) = 0 → f = 0

variable {Xo c U}

theorem supE_cusp_ne_top {a n} {σ : c.F →+* ℂ} (hσ : GoodEmb c σ) {f : Rul Xo c} (hf : f ∈ cusp Xo c U a n) :
    supE (U σ).X (laU (U σ) a n) (rdU (U σ) f) ≠ ⊤ := by
  unfold cusp at hf
  have h1 := (Submodule.mem_inf.mp hf).2
  have h2 := (Submodule.mem_iInf _).mp ((Submodule.mem_iInf _).mp h1 σ) hσ
  exact supE_ne_top _ _ (Submodule.mem_comap.mp h2)

variable (U)

variable {U} {σ : c.F →+* ℂ}

end Formalism.L2.PjFree
