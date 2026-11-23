module

public import Mathlib
public import Formalism.LocalToGlobal.ProjectiveLattices.ThShort
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.ThetaValues.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAdelicOne
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0179
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.SlopeBoundSingleLiftOfDefinitions
public import Development.AbelianVarietyTheory.Definitions.Divisors.CompEqOneIffPush
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
section
noncomputable section

namespace GlobalTheory.LevPull

open NumberField Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

def IntAt (Xo : Moduli Dw l) (c : Coeff l) (f : Rul Xo c) : Prop := ∀ la, ∀ v ∈ valSet Xo c (algCls Xo c) la, 0 ≤ v f

def Pull (d : DeltaDat Xo c 0) (f : Rul Xo c) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → evR d.Xo₂ d.c₂ g y₂ = evR Xo c f y

def FibConst (d : DeltaDat Xo c 0) (g : Rul d.Xo₂ d.c₂) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [Algebra c.F k] [Algebra d.c₂.F k],
    (∀ a : c.F, algebraMap d.c₂.F k (d.eF a) = algebraMap c.F k a) →
    ∀ (y₂ y₂' : FrPt d.Xo₂ d.c₂ k) (y : FrPt Xo c k), FrOver d y₂ y → FrOver d y₂' y →
      evR d.Xo₂ d.c₂ g y₂ = evR d.Xo₂ d.c₂ g y₂'

theorem Pull.fibConst {d : DeltaDat Xo c 0} {f : Rul Xo c} {g : Rul d.Xo₂ d.c₂} (h : Pull d f g) : FibConst d g :=
  fun k _ _ _ _ hk y₂ y₂' y h₁ h₂ => (h k hk y₂ y h₁).trans (h k hk y₂' y h₂).symm


variable (Dw l) in
abbrev LaQ : Type := Dw.La ⧸ (l.Mb • ⊤ : Submodule (𝓞 E) Dw.La)


variable (Dw l) in
abbrev Gam : Type := LaQ Dw l ≃ₗ[𝓞 E] LaQ Dw l

def IsLift (lift : Gam Dw l → Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ γ, (Submodule.mkQ _) ∘ₗ lift γ = γ.toLinearMap ∘ₗ Submodule.mkQ _

def CongMod (I : Ideal (𝓞 E)) (h h' : Dw.La →ₗ[𝓞 E] Dw.La) : Prop :=
  ∀ a, h a - h' a ∈ (I • ⊤ : Submodule (𝓞 E) Dw.La)

end GlobalTheory.LevPull
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
section
noncomputable section

namespace GlobalTheory.DefPt

open CategoryTheory NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.DualWeyl GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.Frames
  GlobalTheory.CompHt ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix Classical

section Point

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

abbrev Mats (Dw : Datum H) (S : Type) : Type := ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S

def part (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → ℕ := fun τ i => a (τ, i)

def Reads (Z : Comp Xo c) (y₀ : FrPt Xo c c.F) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (x : TIdx (part Dw a) → c.F) (f : Rul Xo c) :
    Prop :=
  f ∈ suppOn Z ∧ ∀ (S : Type) [CommRing S] [Algebra c.F S] (z y : FrPt Xo c S) (Y : Mats Dw S) (s : S),
    (∀ τ, IsUnit (Y τ).det) → IsUnit s → FrMap (Algebra.ofId c.F S) y₀ z → FrChg (fun τ => (Y τ)ᵀ) s z y →
      evR Xo c f y = s ^ n * tval (part Dw a) (fun I => algebraMap c.F S (x I)) Y

def LocFr (y₀ : FrPt Xo c c.F) (w : HeightOneSpectrum (𝓞 c.F)) (a : c.F) (B : Mats Dw c.F) : Prop :=
  a ≠ 0 ∧ (∀ τ, (B τ).det ≠ 0) ∧
    ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa w T.V io e → letI := io.toAlgebra
      ∀ y z : FrPt Xo c T.Fr, Integral T io y → FrMap (Algebra.ofId c.F T.Fr) y₀ z → y.x = z.x →
        ∃ (Y : Mats Dw T.V) (u : T.Vˣ), (∀ τ, IsUnit (Y τ).det) ∧
          FrChg (fun τ => ((B τ).map io * (Y τ).map (algebraMap T.V T.Fr))ᵀ) (io a * algebraMap T.V T.Fr u) z y

def ArchFr (y₀ : FrPt Xo c c.F) (σ : c.F →+* ℂ) (N : ℝ) (X : Mats Dw ℂ) : Prop :=
  0 < N ∧ (∀ τ, (X τ).det ≠ 0) ∧
    ∀ z y : FrPt Xo c (CAt σ), FrMap (Algebra.ofId c.F (CAt σ)) y₀ z → FrChg (S := CAt σ) (fun τ => (X τ)ᵀ) 1 z y →
      GlobalTheory.LamT.IsMetric y N fun _ => 1

structure PtData (Z : Comp Xo c) : Type where

  y₀ : FrPt Xo c c.F
  on : LiesOn Z y₀
  only : ∀ (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S), LiesOn Z y → y.x = spMap (algebraMap c.F S) ≫ y₀.x

  a : HeightOneSpectrum (𝓞 c.F) → c.F

  B : HeightOneSpectrum (𝓞 c.F) → Mats Dw c.F
  loc : ∀ w, LocFr y₀ w (a w) (B w)
  fin : {w | ¬ (a w = 1 ∧ B w = 1)}.Finite

  N : (c.F →+* ℂ) → ℝ

  X : (c.F →+* ℂ) → Mats Dw ℂ
  arch : ∀ σ, ArchFr y₀ σ (N σ) (X σ)

namespace PtData

variable {Z : Comp Xo c} (P : PtData Z)

def degLie (τ : E →+* ℂ) : ℝ := detDeg (fun w => P.B w τ) fun σ => P.X σ τ

def degTh : ℝ := lineDeg (fun σ => (Real.sqrt (P.N σ))⁻¹) fun w => (vAdd w (P.a w) : ℝ)

def matA (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (w : HeightOneSpectrum (𝓞 c.F)) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) c.F := fibA (part Dw a) (P.a w ^ n) (P.B w)

def matY (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (σ : c.F →+* ℂ) :
    Matrix (TIdx (part Dw a)) (TIdx (part Dw a)) ℂ := fibY (part Dw a) ((Real.sqrt (P.N σ))⁻¹ ^ n) (P.X σ)

end PtData

variable {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (ξ : ℝ)

def FibreAt (Z : Comp Xo c) (G : WTZ E) (s : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (_ : Nonempty ι) (L : Submodule (𝓞 c.F) (ι → c.F))
    (Y : (c.F →+* ℂ) → Matrix ι ι ℂ) (φ : (ι → c.F) →ₗ[c.F] Rul Xo c),
    Submodule.IsFullLattice c.F L ∧ (∀ σ, (Y σ).det ≠ 0) ∧ s ≤ slope_sq (matNorm Y) L / 2 ∧ Function.Injective φ ∧
    LinearMap.range φ = cuspOn U Z G ∧ (∀ x ∈ L, ∀ w, ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (φ x)) ∧
    ∀ σ x, ∀ z ∈ framesOn (U (goodOf c σ)) Z, homN (U (goodOf c σ)) ξ G (φ x) z ≤ matNorm Y σ x

def defBound (Dw : Datum H) (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (c₁ : ℝ) : ℝ :=
  (∑ τ : Psi H, (((size (part Dw a τ.1) : ℝ) / Dw.p + (n : ℝ) / 2) * c₁ - Real.log (dim (part Dw a τ.1)) / 2)) +
    (n : ℝ) * ((Fintype.card (Psi H) : ℝ) * Dw.p) * (Real.log (2 * Real.pi) / 4 - GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects.lrd E / 2)

structure DefCase : Prop where
  q : Dw.q = 0
  p : 1 ≤ Dw.p
  good : ∀ p : ℕ, p.Prime → l.GoodAt p
  A : l.A = 1
  geo : FnAlgClosed (Xo := Xo) (c := c)
  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)
  xi : ∀ σ, GoodEmb c σ → ∀ k (τ : E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = ξ


variable (Xo c) in
def FreePt {G : Type} [Group G] (lev : G → (Dw.La →ₗ[𝓞 E] Dw.La) × (Dw.La →ₗ[𝓞 E] Dw.La)) : Prop :=
  ∀ (g : G) (k : Type) [Field k] [Algebra c.F k] (y y' : FrPt Xo c k), levR (lev g) y y' → y'.x = y.x → g = 1

end Point

section Eigen

variable {D : D7} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) {G : Type} [Group G]
  (lev : G → (Dw.La →ₗ[𝓞 D.host.E] Dw.La) × (Dw.La →ₗ[𝓞 D.host.E] Dw.La)) (χ : G →* (c.F)ˣ)


set_option synthInstance.maxHeartbeats 400000 in
def eigSub : Submodule c.F (Rul Xo c) :=
  ⨅ g : G, LinearMap.ker (actLev (Xo := Xo) c lev g - ((χ g : (c.F)ˣ) : c.F) • (LinearMap.id : Rul Xo c →ₗ[c.F] Rul Xo c))

def eigLat (W : WTZ D.host.E) : Submodule (𝓞 c.F) (cuspW Xo c U W) :=
  latW U W ⊓ ((eigSub lev χ).comap (cuspW Xo c U W).subtype).restrictScalars (𝓞 c.F)

end Eigen

end GlobalTheory.DefPt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.GenOf
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

def TyEll : GlobalTheory.CongL.UnitaryAutomorphicTypeClass := fun E _ _ _ l a w₀ U =>
  ∃ (m : ℕ) (J : Subgroup (GL (Fin a) (w₀.adicCompletion E))) (θ : J →* Multiplicative (ZMod (l ^ m)))
    (χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ),
    IsOpen (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧ IsCompact (J : Set (GL (Fin a) (w₀.adicCompletion E))) ∧
    (∀ x ∈ J, ∀ k : ℕ, 0 < k → x ^ k = 1 → x = 1) ∧ Function.Surjective θ ∧ χ ≠ 1 ∧
    (∀ (σ : SmIrr (GL (Fin a) (w₀.adicCompletion E))) (v : σ.V), v ≠ 0 →
      (∀ g : J, σ.ρ g v = ((χ (θ g) : ℂˣ) : ℂ) • v) → GlobalTheory.SmGL.IsCuspidal σ.ρ) ∧
    ∃ φ ∈ U, φ ≠ 0 ∧ ∀ x ∈ locU a w₀, ∀ h : cLoc w₀ x ∈ J, RU E a x φ = ((χ (θ ⟨cLoc w₀ x, h⟩) : ℂˣ) : ℂ) • φ

def GenOf (D : ∀ a : ℕ, MvPolynomial (Fin a) ℤ) : ℕ → ℕ → Multiset ℂˣ → Prop := fun a _ B =>
  ∀ α : Fin a → ℂˣ, Finset.univ.val.map α = B → MvPolynomial.aeval (fun i => (α i : ℂ)) (D a) ≠ 0

end GlobalTheory.CongW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.KottwitzDimSignatureOneOne
section
noncomputable section

namespace GlobalTheory.UPel.Sm.Model

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

section Univ
variable {F : Type} [Field F] [NumberField F] [IsCMField F] {D : Datum F} {p N : ℕ}

end Univ

section KS
variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]
  {ρ : O →+* Module.End k H} {φ : LinearMap.BilinForm k H} {Fil Z : Submodule k H}

def ksSub (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) :
    Submodule k (H →ₗ[k] H) where
  carrier := {f | IsKS ρ φ Fil Z f}
  zero_mem' := ⟨by simp, by simp, by simp⟩
  add_mem' {f g} hf hg := ⟨fun a x hx => by
      convert add_mem (hf.1 a x hx) (hg.1 a x hx) using 1
      simp only [LinearMap.add_apply, map_add (f := _)]; abel,
    fun x hx => add_mem (hf.2.1 x hx) (hg.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      have h2 := hg.2.2 x hx y hy
      simp only [LinearMap.add_apply, map_add (f := _)]
      linear_combination h1 + h2⟩
  smul_mem' c f hf := ⟨fun a x hx => by
      convert Fil.smul_mem c (hf.1 a x hx) using 1
      simp only [LinearMap.smul_apply, map_smul, smul_sub],
    fun x hx => Fil.smul_mem c (hf.2.1 x hx), fun x hx y hy => by
      have h1 := hf.2.2 x hx y hy
      simp only [LinearMap.smul_apply, map_smul, smul_eq_mul]
      linear_combination c * h1⟩

def cls (Fil : Submodule k H) : (H →ₗ[k] H) →ₗ[k] (Fil →ₗ[k] H ⧸ Fil) where
  toFun f := Fil.mkQ ∘ₗ f ∘ₗ Fil.subtype
  map_add' f g := by ext; simp
  map_smul' c f := by ext; simp

theorem cls_eq_iff (f g : H →ₗ[k] H) : cls Fil f = cls Fil g ↔ ∀ x ∈ Fil, f x - g x ∈ Fil := by
  simp [cls, LinearMap.ext_iff, Submodule.Quotient.eq]

theorem KSDim.rank_eq {d : ℕ} (h : KSDim ρ φ Fil Z d) :
    Module.rank k ((ksSub ρ φ Fil Z).map (cls Fil)) = d := by
  obtain ⟨f, hf, hu⟩ := h
  have key : ∀ (g : H →ₗ[k] H) (c : Fin d → k), (∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil) ↔
      cls Fil g = ∑ i, c i • cls Fil (f i) := fun g c => by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [← map_smul, ← map_sum, cls_eq_iff, LinearMap.sum_apply, LinearMap.smul_apply]
  have li : LinearIndependent k fun i => cls Fil (f i) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    obtain ⟨c₀, -, h₀⟩ := hu 0 (ksSub ρ φ Fil Z).zero_mem
    have := (h₀ c ((key 0 c).2 (by rw [hc, map_zero]))).trans (h₀ 0 ((key 0 0).2 (by simp))).symm
    exact congrFun this
  have : (ksSub ρ φ Fil Z).map (cls Fil) = Submodule.span k (Set.range fun i => cls Fil (f i)) := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      obtain ⟨c, hc, -⟩ := hu g hg
      rw [(key g c).1 hc]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨f i, hf i, rfl⟩
  rw [this, rank_span li, ← Cardinal.lift_inj.{_, 0}, Cardinal.mk_range_eq_of_injective li.injective]
  simp

theorem KSDim.unique {d e : ℕ} (h : KSDim ρ φ Fil Z d) (h' : KSDim ρ φ Fil Z e) : d = e := by
  exact_mod_cast (KSDim.rank_eq h).symm.trans (KSDim.rank_eq h')

end KS

section Examples
variable (k : Type) [Field k]

end Examples

end GlobalTheory.UPel.Sm.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Multiplier
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.DegCmp

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal

section Generic

variable {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V] [Field Ω] [Algebra K Ω]

def hilb (ev : V →ₗ[K] Ω) (τ : ℕ) : ℕ∞ :=
  Cardinal.toENat (Module.rank K (↥((LinearMap.range ev) ^ τ : Submodule K Ω)))

def coneAlg (ev : V →ₗ[K] Ω) : Subalgebra K (Polynomial Ω) :=
  Algebra.adjoin K (Set.range fun v => Polynomial.X * Polynomial.C (ev v))

def IsIntDeg (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  IsIntegral (coneAlg ev) (Polynomial.X ^ τ * Polynomial.C t : Polynomial Ω)

def IsRatio (ev : V →ₗ[K] Ω) (τ : ℕ) (t : Ω) : Prop :=
  ∃ (e : ℕ) (h : Ω), h ∈ ((LinearMap.range ev) ^ e : Submodule K Ω) ∧ h ≠ 0 ∧
    t * h ∈ ((LinearMap.range ev) ^ (τ + e) : Submodule K Ω)

end Generic

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Indef.Tree

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ)

def UnfAll : Prop := ∀ σ, GoodEmb c σ → IsUnf (U σ)

def Proport : Prop :=
  ∀ (Z : Comp Xo c) (la : Weight Dw), (∀ τ, StrictAnti (la τ)) →
    growthOn U Z (wtOf Dw la 0) = ENNReal.ofReal (topDeg U Z la)

def EqVolume : Prop := ∀ Z Z' : Comp Xo c, vZero U Z = vZero U Z'

set_option synthInstance.maxHeartbeats 100000 in
def RatioOn (Z : Comp Xo c) (G : WTZ E) : Prop :=
  ∀ (τ : ℕ), ∀ t ∈ cuspOn U Z (τ • G), IsRatio (genPoint Z (cuspOn U Z G)) τ (genVal Z t)

end GlobalTheory.DegCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NotIsChowFormIntLineZero
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHt.Test

open MvPolynomial NumberField IsDedekindDomain Module Filter GlobalTheory.ChowHt GlobalTheory.AllWt GlobalTheory.CompHt
open scoped ENNReal


set_option autoImplicit false in
open MvPolynomial NumberField IsDedekindDomain Module Filter in
open scoped ENNReal in
theorem _root_.GlobalTheory.CompHt.Test.imageDeg_zero {K V Ω : Type} [Field K] [AddCommGroup V] [Module K V]
    [Field Ω] [Algebra K Ω] (D : ℕ) :
    _root_.GlobalTheory.CompHt.imageDeg (0 : V →ₗ[K] Ω) D = 0 := by
  by_contra hne
  obtain ⟨N, b, f, hf⟩ := (_root_.GlobalTheory.CompHt.imageDeg_pos_iff _ D).1 (Nat.pos_of_ne_zero hne)
  obtain ⟨y, hy, hI⟩ := hf.exists_point
  apply hy
  funext i
  have hX : (X i : MvPolynomial (Fin N) K) ∈ _root_.GlobalTheory.CompHt.imageIdeal (0 : V →ₗ[K] Ω) b := by
    unfold _root_.GlobalTheory.CompHt.imageIdeal
    rw [_root_.GlobalTheory.CompHt.mem_coneIdeal_of_isHomogeneous _ (isHomogeneous_X K i)]
    simp
  simpa using hI _ hX

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

end GlobalTheory.CompHt.Test
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.Subsingleton
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField

namespace GlobalTheory.IwLevel

open GlobalTheory.UPel.HT

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S S' : Scheme.{0}}

def htAct {s : S ⟶ Sp R} (o : Obj b N s) : Out.RingAct o.A D.O :=
  ⟨o.act.act, o.act.hom, o.act.one, o.act.mul, o.act.add⟩

@[simp] theorem htAct_act {s : S ⟶ Sp R} (o : Obj b N s) (c : D.O) : (htAct o).act c = o.act.act c := rfl

abbrev HTIw {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) : Type 1 :=
  Chain (htAct o) (w.map (algebraMap (𝓞 D.F) D.O)) (Ideal.absNorm w ^ D.m) D.n

section Basic₂

end Basic₂

end GlobalTheory.IwLevel
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.WtSizeOver
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}


open Classical in
def wtSizeOver (ι : Qbar l ≃+* ℂ) (lam : (E →+* ℂ) → DomWeight a) (u : HeightOneSpectrum (𝓞 E)) : ℕ :=
  ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => OverPair ι u τ), ∑ k : Fin a, ((lam τ).w k).natAbs

end GlobalTheory.CongW

end
end

