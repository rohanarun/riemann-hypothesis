module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDefiniteDatumGoodObj
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsKSValueOneOfRetraction
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsIntegralOpW
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0013
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LeviBlockCentreFinite
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0018
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0020
public import Formalism.LocalToGlobal.CMDeterminantIdeals.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0060
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatB

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.InclEquiv
section
set_option autoImplicit false

noncomputable section

open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.Adelic GlobalTheory.HermTools GlobalTheory.HilbertSamuel GlobalTheory.HSCore GlobalTheory.Vanishing

namespace GlobalTheory.HSShort

variable {F : Type} [Field F] [NumberField F]

abbrev Tot (G : Geo F) : Type := ∀ j, G.Sec j

def shiftAt (G : Geo F) (u : Fin G.N → F) : ∀ j, Tot G →ₗ[F] G.Sec j
  | 0 => 0
  | j + 1 => G.mulW j u ∘ₗ LinearMap.proj j

def shift (G : Geo F) : (Fin G.N → F) →ₗ[F] Module.End F (Tot G) where
  toFun u := LinearMap.pi (shiftAt G u)
  map_add' u v := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]
  map_smul' c u := LinearMap.ext fun x => funext fun j => by cases j <;> simp [shiftAt]

def incl (X : Data F) (j : ℕ) : X.V j →ₗ[F] Tot X.toGeo := LinearMap.single F _ j ∘ₗ (X.V j).subtype

theorem incl_injective (X : Data F) (j : ℕ) : Function.Injective (incl X j) := fun a b h =>
  Subtype.ext (by simpa [incl] using congrFun h j)

def inclEquiv (X : Data F) (j : ℕ) : X.V j ≃ₗ[F] LinearMap.range (incl X j) := LinearEquiv.ofInjective _ (incl_injective X j)

def sysOf (X : Data F) (Λ₀ : ℝ) : Sys F (Tot X.toGeo) where
  N := X.N
  n := X.n
  D := X.D
  T := X.T
  w := X.w
  fr := X.A
  mul := shift X.toGeo
  V j := LinearMap.range (incl X j)
  M j := (X.M j).map ((inclEquiv X j).toLinearMap.restrictScalars (𝓞 F))
  nm j := comap (X.nm j) (inclEquiv X j).symm.toLinearMap (inclEquiv X j).symm.injective
  beta := X.beta
  abelian₂ := X.abelian₂
  Lam0 := Λ₀
  LamD := X.LamD
  LamT := X.LamT

def totExt (G : Geo F) (E : Type) [Field E] [NumberField E] [Algebra F E] :
    Tot G →ₛₗ[algebraMap F E] Tot (G.baseChange E) where
  toFun x j := G.toExt E j (x j)
  map_add' x y := funext fun j => map_add _ _ _
  map_smul' c x := funext fun j => map_smulₛₗ (G.toExt E j) c (x j)

section Split

variable {X : Data F} {s : Fin X.D → Fin X.N → F} {hs : X.IsGood s} {δ : ℕ}

def totRes (Co : Coord X.toGeo hs δ) : Tot X.toGeo →ₗ[F] (Fin δ → F) :=
  (Co.ev 0).toLinearMap ∘ₗ hs.res 0 ∘ₗ LinearMap.proj 0


variable (X s) in
def totFil (a : ℕ) : Submodule F (Tot X.toGeo) := (filV X s a).map (incl X X.T)

def totSym (Co : Coord X.toGeo hs δ) (a : ℕ) : totFil X s a →ₗ[F] (MonoDeg (Fin X.D) a × Fin δ → F) :=
  symV Co a ∘ₗ (Submodule.equivMapOfInjective _ (incl_injective X X.T) (filV X s a)).symm.toLinearMap

end Split

end GlobalTheory.HSShort
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
section
noncomputable section

namespace GlobalTheory.UPel.Sm

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel

variable {F : Type} [Field F] [NumberField F] [IsCMField F]

section KS

variable {k H O : Type*} [Field k] [AddCommGroup H] [Module k H] [Ring O]

def IsKS (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H)
    (f : H →ₗ[k] H) : Prop :=
  (∀ a, ∀ x ∈ Fil, f (ρ a x) - ρ a (f x) ∈ Fil) ∧ (∀ x ∈ Z, f x ∈ Fil) ∧
    ∀ x ∈ Fil, ∀ y ∈ Fil, φ (f x) y + φ x (f y) = 0

def KSDim (ρ : O →+* Module.End k H) (φ : LinearMap.BilinForm k H) (Fil Z : Submodule k H) (d : ℕ) :
    Prop :=
  ∃ f : Fin d → (H →ₗ[k] H), (∀ i, IsKS ρ φ Fil Z (f i)) ∧
    ∀ g, IsKS ρ φ Fil Z g → ∃! c : Fin d → k, ∀ x ∈ Fil, g x - ∑ i, c i • f i x ∈ Fil

end KS

end GlobalTheory.UPel.Sm
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.OverPair
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong Formalism.UG

namespace GlobalTheory.CongW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime]

def OverPair (ι : Qbar l ≃+* ℂ) (w₀ : HeightOneSpectrum (𝓞 E)) (τ : E →+* ℂ) : Prop :=
  (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (x : E))‖ < 1) ∨
    (∀ x : 𝓞 E, x ∈ w₀.asIdeal → ‖ι.symm (τ (IsCMField.complexConj E (x : E)))‖ < 1)

end GlobalTheory.CongW
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
section
namespace GlobalTheory.ThK

structure KP : Prop where

  base : GlobalTheory.FunPr.Hypotheses₂

  howeDualityUnitary : GlobalTheory.Published.HoweDualityUnitary

  howeDualityReal : GlobalTheory.Published.HoweDualityReal

  automorphicFormsUnitary : GlobalTheory.Published.AutomorphicFormsUnitary

  eisensteinIsotropicLine : GlobalTheory.Published.EisensteinIsotropicLine

  genericityGL : GlobalTheory.Published.GenericityGL

  complementaryThetaInert : GlobalTheory.Published.ComplementaryThetaInert

  siegelSetUnitary : GlobalTheory.Published.SiegelSetUnitary

  minguezThetaGL : GlobalTheory.Published.MinguezThetaGL

  jacquetShalika : GlobalTheory.Published.JacquetShalika

  discreteSpectrumGL : GlobalTheory.Published.DiscreteSpectrumGL

  heckeTateFunctionalEquation : GlobalTheory.Published.HeckeTateFunctionalEquation

  automorphicFormsFiniteUnitary : GlobalTheory.Published.AutomorphicFormsFiniteUnitary

  geometricLemmaFiltration : GlobalTheory.Published.GeometricLemmaFiltration

  cuspidalSpectrumGL : GlobalTheory.Published.CuspidalSpectrumGL

  siegelWeilAnisotropicCM : GlobalTheory.Published.SiegelWeilAnisotropicCM

  siegelWeilAnisotropicHermitian : GlobalTheory.Published.SiegelWeilAnisotropicHermitian

  siegelEisensteinDoubled : GlobalTheory.Published.SiegelEisensteinDoubled

  leviCentreFiniteUnitary : GlobalTheory.Published.LeviCentreFiniteUnitary

  leviBlockCentreFinite : GlobalTheory.Published.LeviBlockCentreFinite

  leviCentreInducedUnitary : GlobalTheory.Published.LeviCentreInducedUnitary

  eisensteinResidueLine : GlobalTheory.Published.EisensteinResidueLine

  rallisTowerUnitary : GlobalTheory.Published.RallisTowerUnitary

end GlobalTheory.ThK
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
section
noncomputable section

namespace GlobalTheory.LevGeo

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.L2.Theta Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure Laws (D : D7) (j : ℕ) {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
    (c : Coeff l) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r)
    (dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r) : Prop where

  inR : InR D j

  host : H.d = D.host.d ∧ (H.rt : D.host.E) = D.host.sqrtMinusD ∧ H.rt0 = D.host.φ₀ D.host.sqrtMinusD ∧
    ∀ t : D.what₂.Tau, DV.tauEmb D t (H.rt : D.host.E) = H.rt0

  dat : IsDatW D j Dw

  levA : l.A = 1

  unf : ∀ σ, GoodEmb c σ → IsUnf (U σ)

  chiTriv : ∀ σ, GoodEmb c σ → ∀ a n, Dom a n → ∀ k, ∀ γ ∈ ((U σ).X k).Γ, ((U σ).X k).χ (laU (U σ) a n k) γ = 1

  dictU : ∀ σ, GoodEmb c σ → ∃ Kf th hr, IsLevelK (D.sp.W j) l.M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
    DictIsUnif (D.sp.W j) (dict σ) Kf th hr ∧
    ∀ g τ k, ‖dmin ((U σ).X (dict σ g).1).Gm (dict σ g).2 τ k‖ = 1

  modelW : ∀ σ, GoodEmb c σ → ∃ hr : (D.sp.W j).rank = D.R.r, ∀ k, ModelW (D.sp.W j) hr ((U σ).X k)

section Derived

variable {D : D7} {j : ℕ} {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l}
  {c : Coeff l} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ D.R.r}
  {dict : ∀ σ : c.F →+* ℂ, GA D (D.sp.W j) → Σ k, Frame ((U σ).X k).Ψ D.R.r}

theorem Laws.unTest (_ : Laws D j Xo c U dict) : ∀ σ, GoodEmb c σ → ∀ k x,
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) ((U σ).un k x) := fun σ _ k x =>
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  GlobalTheory.TransferCompare.allTest_framed Xo c (CAt σ) ((U σ).un k x)

theorem Laws.xiAbs (h : Laws D j Xo c U dict) : ∀ σ, GoodEmb c σ → ∀ k (τ : D.host.E →+* ℂ), ‖τ ((U σ).X k).ξ0‖ = xiR D := by
  intro σ hσ k τ
  obtain ⟨hr, hm⟩ := h.modelW σ hσ
  rw [(hm k).2, map_neg, norm_neg]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatB.norm_embedding_hostFormConstant_eq D τ

end Derived

def coreDict {D : D7} (T : Core D) (j : ℕ) (σ : T.Q.c.F →+* ℂ) (g : GA D (D.sp.W j)) : Σ k, Frame ((T.U j σ).X k).Ψ D.R.r :=
  open Classical in if h : T.V j σ = D.sp.W j then T.dict j σ (h ▸ g) else T.dict j σ 1

theorem unif_of_space_eq {D : D7} {r : ℕ} {C : Type} {X : C → Data D.host.E r} (V W : HSp D) (h : V = W)
    (dict : GA D V → Σ k, Frame (X k).Ψ r) (M : ℕ) (Kf : Subgroup (GA D V)) (hK : IsLevelK V M Kf)
    (hd : ∃ th hr, (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧ DictIsUnif V dict Kf th hr)
    (hu : ∀ g τ k, ‖dmin (X (dict g).1).Gm (dict g).2 τ k‖ = 1) :
    ∃ Kf th hr, IsLevelK W M Kf ∧ (∀ k τ, Formalism.MainNotions.StandardLattice.IsInfEmb τ.1 (th k τ)) ∧
      DictIsUnif W (fun g => dict (h ▸ g)) Kf th hr ∧
      ∀ (g : GA D W) τ k, ‖dmin (X (dict (h ▸ g)).1).Gm (dict (h ▸ g)).2 τ k‖ = 1 := by
  subst h
  obtain ⟨th, hr, h1, h2⟩ := hd
  exact ⟨Kf, th, hr, hK, h1, h2, hu⟩

theorem laws_core (D : D7) (T : CoreJ D) (j : ℕ) (h : LawsJ T) (hj : InR D j) :
    Laws D j (T.Q.Xo j) T.Q.c (T.U j) (coreDict T.toCore j) := by
  refine ⟨hj, h.pins.1, h.pins.2.2.2 j hj, h.pins.2.1.2, h.unf j hj, h.chiTriv j hj, ?_, ?_⟩
  · intro σ hσ
    have hV := h.spaceW j hj σ hσ
    have e : coreDict T.toCore j σ = fun g => T.dict j σ (hV ▸ g) := by
      funext g
      simp only [coreDict, dite_eq_left hV]
    rw [e, h.pins.2.1.1]
    exact unif_of_space_eq _ _ hV (T.dict j σ) _ (T.Kf j σ) (h.levelK j hj σ hσ) (h.dictU j hj σ hσ)
      (h.muUnit j hj σ hσ).2.2.2
  · intro σ hσ
    have := h.modelW j hj σ hσ
    rw [h.spaceW j hj σ hσ] at this
    exact this

section Consts

variable (E : Type) [Field E] [NumberField E] (r : ℕ)

def chartRad (w : ℝ) : ℝ := 1 / (200 * (r : ℝ) ^ 3 * (w + fdeg E))

def multBd (ε : ℝ) : ℝ := (1 + 2 * (2 * (fdeg E : ℝ) * r) ^ 2 * dE E / ε) ^ (2 * fdeg E * r ^ 2)

def dimFl : ℕ := fdeg E * (r * (r - 1) / 2)

def locConst (w ε : ℝ) : ℝ :=
  8 * ((dimFl E r).factorial : ℝ) / (Real.pi * chartRad E r w ^ 2) ^ dimFl E r * multBd E r ε

def massLev (M : ℕ) : ℝ := GlobalTheory.UCls.massBd E r M (classNumber E * M ^ (2 * fdeg E))

def epsLev (d M : ℕ) (w : ℝ) : ℝ := epStar (2 * M * Real.sqrt d) (fdeg E) w 1

def supConst (d M : ℕ) (w : ℝ) : ℝ := locConst E r w (epsLev E d M w) * massLev E r M

def cmLen (q d M : ℕ) (w : ℝ) : ℝ :=
  frameBasisRadius r q (fdeg E) (dE E) (Real.sqrt (epsLev E d M w)) (3 * frameRadius w r / 5)

def lamSup (q d M : ℕ) (Om s t : ℝ) : ℝ :=
  (Formalism.L2.LamCM.pDeg Om + 1 / 2 * Real.log (cmLen E r q d M (s + t + 1))) * (s + t) +
    s * Real.log (r * cmLen E r q d M (s + t + 1))

def lamPet (q d M : ℕ) (Om s t : ℝ) : ℝ := lamSup E r q d M Om s t + 1 / 2 * Real.log (supConst E r d M (s + t + 1))

theorem one_le_multBd {ε : ℝ} (hε : 0 < ε) : 1 ≤ multBd E r ε := by
  unfold multBd
  refine one_le_pow₀ (le_add_of_nonneg_right ?_)
  have : 0 ≤ dE E := abs_nonneg _
  positivity

end Consts

def absA {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) : ℕ := ∑ b : E →+* ℂ, ∑ i : Fin (Dw.mult b), a (b, i)

end GlobalTheory.LevGeo
end
end

