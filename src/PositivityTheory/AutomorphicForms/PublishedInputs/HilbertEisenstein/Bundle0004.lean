module

public import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SSmooth
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0043
public import Mathlib
public import GroundTheory.GlobalFields.TateThesis.Bundle0002
public import GroundTheory.GlobalFields.TateThesis.AdelePoisson
public import GroundTheory.GlobalFields.TateThesis.TateThetaDecay

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.LibOpenLevel
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published
open _root_.Matrix UpperTheory.V.Af.GlobalFixedVectors

namespace UpperTheory.HilbertEisensteinWeightOne.LibOpenLevel

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

private theorem local_mem_principal_congruence {M : ℕ} (w : HeightOneSpectrum (𝓞 F)) (c : ℕ)
    (hM : (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)
    {k : GL (Fin 2) (Af F)} (hk : k ∈ KLev F 2 M) : GeneralLinearGroup.map (pLoc F w) k ∈ K1 w c := by
  obtain ⟨g, hg, rfl⟩ := hk
  let p : Ohat F →+* w.adicCompletionIntegers F :=
    ((pLoc F w).comp (Ohat F).subtype).codRestrict (w.adicCompletionIntegers F) fun x => GlobalFixedVectors.mem_Ohat.1 x.2 w
  refine ⟨GeneralLinearGroup.map p g, ?_, Units.ext rfl⟩
  have key : GeneralLinearGroup.map (n := Fin 2)
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c)) (GeneralLinearGroup.map p g) = 1 := by
    let q := Ideal.quotientMap (I := Ideal.span {(M : ↥(Ohat F))}) (IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c) p
      ((Ideal.span_singleton_le_iff_mem _).2 (by simpa using hM))
    have := congrArg (GeneralLinearGroup.map q) (MonoidHom.mem_ker.1 hg)
    rw [map_one] at this
    rw [← this]
    rfl
  exact Subgroup.mem_comap.2 (key ▸ one_mem _)

private theorem exists_level (c : HeightOneSpectrum (𝓞 F) → ℕ) (hc : {w | c w ≠ 0}.Finite) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ w : HeightOneSpectrum (𝓞 F),
      (M : w.adicCompletionIntegers F) ∈ IsLocalRing.maximalIdeal (w.adicCompletionIntegers F) ^ c w := by
  refine ⟨∏ w ∈ hc.toFinset, Ideal.absNorm w.asIdeal ^ c w, ?_, fun w => ?_⟩
  · refine Nat.pos_of_ne_zero (Finset.prod_ne_zero_iff.2 fun w _ => pow_ne_zero _ ?_)
    exact fun h => w.ne_bot (Ideal.absNorm_eq_zero_iff.1 h)
  · by_cases h : c w = 0
    · simp [h]
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun w : HeightOneSpectrum (𝓞 F) => Ideal.absNorm w.asIdeal ^ c w)
      (hc.mem_toFinset.2 h)
    rw [hm, Nat.cast_mul, Nat.cast_pow]
    refine Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow ?_ _)
    have h1 := Ideal.absNorm_mem w.asIdeal
    rw [← map_natCast (algebraMap (𝓞 F) (w.adicCompletionIntegers F))]
    generalize (Ideal.absNorm w.asIdeal : 𝓞 F) = x at h1
    refine (Valuation.mem_maximalIdeal_iff _ (Valued.v : Valuation (w.adicCompletion F) _)).2 ?_
    have h2 : Valued.v (algebraMap (𝓞 F) (w.adicCompletion F) x) < 1 := by
      rw [IsScalarTower.algebraMap_apply (𝓞 F) F (w.adicCompletion F)]
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _).trans_lt ((w.valuation_lt_one_iff_mem x).2 h1)
    exact h2

theorem finite_support {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) :
    {w | c w ≠ 0}.Finite := by
  obtain ⟨m, hm, hω⟩ := isOfFinOrder_iff_pow_eq_one.1 hH.fin
  have ho := GlobalTheory.HeckeGal.isOpen_ker_of_pow ω.1 ω.2.1 hm fun x => by
    have := congrArg (fun ξ : HChar F => ξ.1 x) hω
    simpa using this
  obtain ⟨S, M, hS, key⟩ := GlobalTheory.OpenIdeleCongr.localIdele_mem_of_isOpen ω.1.ker ho
  refine hS.subset fun w hw => ?_
  by_contra hwS
  exact hw (Nat.le_zero.1 ((hH.cond w).2 fun x hu _ => MonoidHom.mem_ker.1 (key w x hu fun h => absurd h hwS)))


variable (F) in
def Kc (c : HeightOneSpectrum (𝓞 F) → ℕ) : Subgroup (GL (Fin 2) (Af F)) :=
  ⨅ w, (K1 w (c w)).comap (GeneralLinearGroup.map (pLoc F w))

theorem mem_Kc {c : HeightOneSpectrum (𝓞 F) → ℕ} {k : GL (Fin 2) (Af F)} :
    k ∈ Kc F c ↔ ∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w) := by
  simp [Kc, Subgroup.mem_iInf]

theorem isOpen_Kc {c : HeightOneSpectrum (𝓞 F) → ℕ} (hc : {w | c w ≠ 0}.Finite) : IsOpen (Kc F c : Set (GL (Fin 2) (Af F))) := by
  obtain ⟨M, hM1, hM⟩ := exists_level c hc
  exact Subgroup.isOpen_mono (fun k hk => mem_Kc.2 fun w => local_mem_principal_congruence w _ (hM w) hk) (isOpen_KLev hM1)

def stab (φ : UpperTheory.V.TR.Sm F 2) : Subgroup (GL (Fin 2) (Af F)) where
  carrier := {k | UpperTheory.V.TR.finRep F 2 k φ = φ}
  one_mem' := by simp
  mul_mem' := fun {a b} ha hb => by
    simp only [Set.mem_ofPred_eq] at *
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := fun {a} ha => by
    simp only [Set.mem_ofPred_eq] at *
    conv_lhs => rw [← ha]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem isOpen_stab {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c) (φ : UpperTheory.V.TR.Sm F 2)
    (h : ∀ k ∈ Kc F c, UpperTheory.V.TR.finRep F 2 k φ = φ) : IsOpen {k | UpperTheory.V.TR.finRep F 2 k φ = φ} :=
  Subgroup.isOpen_mono (H₂ := stab φ) (fun k hk => h k hk) (isOpen_Kc (finite_support hH))

theorem isOpen_stab_of_glob {ω : HChar F} {c : HeightOneSpectrum (𝓞 F) → ℕ} (hH : Hyp ω c)
    (φ : UpperTheory.V.TR.Sm F 2)
    (h : ∀ k : GL (Fin 2) (Af F), (∀ w, GeneralLinearGroup.map (pLoc F w) k ∈ K1 w (c w)) →
      ∀ g, φ.1 (g * finGL F 2 k) = φ.1 g) :
    IsOpen {k | UpperTheory.V.TR.finRep F 2 k φ = φ} :=
  isOpen_stab hH φ fun k hk => Subtype.ext (funext fun g => h k (mem_Kc.1 hk) g)

end UpperTheory.HilbertEisensteinWeightOne.LibOpenLevel
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.PolyVHasTemperateGrowth
section
noncomputable section

open NumberField
open scoped SchwartzMap ContDiff

namespace UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness

variable (F : Type) [Field F] [NumberField F] [IsTotallyReal F]

def curryE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃ₗ[ℝ] (Fin 2 × InfinitePlace F → ℝ) where
  toFun y p := y p.1 p.2
  invFun z i v := z (i, v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def euclE : (Fin 2 → UpperTheory.V.TR.Rinf F) ≃L[ℝ] EuclideanSpace ℝ (Fin 2 × InfinitePlace F) :=
  (curryE F).toContinuousLinearEquiv.trans (EuclideanSpace.equiv (Fin 2 × InfinitePlace F) ℝ).symm

omit [IsTotallyReal F] in
theorem norm_euclE_sq (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    ‖euclE F y‖ ^ 2 = ∑ v, ((y 0 v) ^ 2 + (y 1 v) ^ 2) := by
  rw [EuclideanSpace.real_norm_sq_eq, Fintype.sum_prod_type, Fin.sum_univ_two,
    ← Finset.sum_add_distrib]
  rfl

def gaussV : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (euclE F) (GroundTheory.Global.gaussianSchwartz _)

theorem gaussV_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    gaussV F y = Complex.exp (-(Real.pi : ℂ) * ∑ v, (((y 0 v : ℝ) : ℂ) ^ 2 + ((y 1 v : ℝ) : ℂ) ^ 2)) := by
  simp only [gaussV, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
    GroundTheory.Global.gaussianSchwartz_apply, norm_euclE_sq]
  push_cast
  rfl

def coordV (i : Fin 2) (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℝ :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : InfinitePlace F => ℝ) v).comp
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => UpperTheory.V.TR.Rinf F) i)

def linV (v : InfinitePlace F) : (Fin 2 → UpperTheory.V.TR.Rinf F) →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp (coordV F 0 v) + Complex.I • Complex.ofRealCLM.comp (coordV F 1 v)

theorem linV_apply (v : InfinitePlace F) (y : Fin 2 → UpperTheory.V.TR.Rinf F) :
    linV F v y = ((y 0 v : ℝ) : ℂ) + Complex.I * ((y 1 v : ℝ) : ℂ) := by
  simp [linV, coordV]

def polyV (y : Fin 2 → UpperTheory.V.TR.Rinf F) : ℂ := ∏ v, linV F v y

theorem polyV_hasTemperateGrowth : (polyV F).HasTemperateGrowth := by
  classical
  have h : ∀ s : Finset (InfinitePlace F),
      (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ s, linV F v y).HasTemperateGrowth := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty]; exact Function.HasTemperateGrowth.const (E := Fin 2 → UpperTheory.V.TR.Rinf F) (1 : ℂ)
    | insert a s ha ih =>
      have e : (fun y : Fin 2 → UpperTheory.V.TR.Rinf F => ∏ v ∈ insert a s, linV F v y) =
          (fun y => linV F a y) * (fun y => ∏ v ∈ s, linV F v y) := by
        funext y
        rw [Finset.prod_insert ha]
        rfl
      rw [e]
      exact (linV F a).hasTemperateGrowth.mul ih
  exact h Finset.univ

def archS : 𝓢(Fin 2 → UpperTheory.V.TR.Rinf F, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (polyV F) (gaussV F)

theorem archS_apply (y : Fin 2 → UpperTheory.V.TR.Rinf F) : archS F y = arch (y 0) (y 1) := by
  rw [archS, SchwartzMap.smulLeftCLM_apply_apply (polyV_hasTemperateGrowth F), gaussV_apply,
    smul_eq_mul, polyV, arch, Finset.prod_mul_distrib, Finset.mul_sum, Complex.exp_sum]
  simp only [linV_apply]

end UpperTheory.HilbertEisensteinWeightOne.EisensteinSmoothness
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def gPt (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : GA F 2 :=
  UpperTheory.V.TR.infGL F 2 (aff y x) * finGL F 2 (aff yf 0)

def yAd (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) : Ad F :=
  ((UpperTheory.V.TR.infId F y * finId F yf : (Ad F)ˣ) : Ad F)

def tau (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : IdeleGroup F :=
  moduleSection (w0 F) t * (u : IdeleGroup F)

def wt (ω : HChar F) (t : {r : ℝ // 0 < r}) (u : normOneSubgroup F) : ℂ :=
  ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ * ((t : ℝ) : ℂ)


variable (F) in
abbrev muE : Measure ({r : ℝ // 0 < r} × normOneSubgroup F) :=
  posRealMeasure.prod ((normOneMeasure F).restrict (normOneFundamentalDomain F))

def zeroRow (c : HeightOneSpectrum (𝓞 F) → ℕ) (τ : IdeleGroup F) : ℂ :=
  ∑' b : Fˣ, Phi c ![0, (τ : Ad F) * algebraMap F (Ad F) (b : F)]

def slice (c : HeightOneSpectrum (𝓞 F) → ℕ) (A : Ad F) (B : Ad F) : ℂ := Phi c ![A, B]

def kern (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (ξ : F) : ℂ :=
  ((ideleModule F τ : ℝ)⁻¹ : ℂ) *
    adelicFourier F (slice c ((τ : Ad F) * Y)) (τ⁻¹ • algebraMap F (Ad F) ξ)

def coefK (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (ξ : F) : ℂ :=
  ∑' a : Fˣ, kern c Y (τ * diagonal F a) ξ

def ex (ξ : F) (x : UpperTheory.V.TR.Rinf F) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ∑ v, (reAt v ξ : ℂ) * (x v : ℂ))


open Classical in
def kernF (c : HeightOneSpectrum (𝓞 F) → ℕ) (A Z : Ad F) : ℂ :=
  (∏ v, (((UpperTheory.V.TR.pInf F A v : ℂ) + (UpperTheory.V.TR.pInf F Z v : ℂ)) *
      Complex.exp (-(Real.pi : ℂ) * ((UpperTheory.V.TR.pInf F A v : ℂ) ^ 2 + (UpperTheory.V.TR.pInf F Z v : ℂ) ^ 2)))) *
    if (∀ w, Valued.v (pLoc F w (pFin F A)) ≤ WithZero.exp (-(c w : ℤ))) ∧
        (∀ w, Valued.v (pLoc F w (pFin F Z)) ≤ WithZero.exp ((c w : ℤ) + dd w))
    then ((finiteAdelicChar F (pFin F Z) : Circle) : ℂ) else 0

def divS (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (𝔪 : Ideal (𝓞 F)) : ℂ :=
  ∑ᶠ 𝔯 ∈ {𝔯 | 𝔯 ∣ 𝔪}, chiI ω c 𝔯

def SKern : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (c : HeightOneSpectrum (𝓞 F) → ℕ),
  {w | c w ≠ 0}.Finite → ∃ κ : ℂ, κ ≠ 0 ∧ ∀ A Z : Ad F, adelicFourier F (slice c A) Z = κ * kernF c A Z

def SFin : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → {w | c w ≠ 0}.Finite

def SZero : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => zeroRow c (tau p.1 p.2) * wt ω p.1 p.2) (muE F)

def SPoint : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (x : UpperTheory.V.TR.Rinf F) (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ (yf : (Af F)ˣ) (τ : IdeleGroup F),
    thetaS (Phi c) (Matrix.GeneralLinearGroup.scalar (Fin 2) τ * gPt x y yf) =
      zeroRow c τ + coefK c (yAd y yf) τ 0 + ∑' ξ : Fˣ, ex (ξ : F) x * coefK c (yAd y yf) τ ξ

def SNull : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ) (yf : (Af F)ˣ) (t : {r : ℝ // 0 < r}),
    IntegrableOn (fun u => coefK c (yAd y yf) (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹) (normOneFundamentalDomain F)
      (normOneMeasure F) →
    ∫ u in normOneFundamentalDomain F, coefK c (yAd y yf) (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ ∂normOneMeasure F = 0

def SAbs : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ yf : (Af F)ˣ,
    (∀ ξ : F, AEStronglyMeasurable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F => coefK c (yAd y yf) (tau p.1 p.2) ξ) (muE F)) ∧
    (∀ p : {r : ℝ // 0 < r} × normOneSubgroup F, Summable fun ξ : Fˣ => ‖coefK c (yAd y yf) (tau p.1 p.2) ξ‖) ∧
    Integrable (fun p : {r : ℝ // 0 < r} × normOneSubgroup F =>
      (∑' ξ : Fˣ, ‖coefK c (yAd y yf) (tau p.1 p.2) ξ‖) * (p.1 : ℝ)) (muE F)

def SUnfold : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∀ (Y : Ad F) (ξ : F),
    Integrable (fun τ : IdeleGroup F => kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ)) (ideleMeasure F) →
    ∫ p, coefK c Y (tau p.1 p.2) ξ * wt ω p.1 p.2 ∂(muE F) =
      ∫ τ, kern c Y τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) ∂ideleMeasure F

def SLocal : Prop := ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ),
  Hyp ω c → ∃ C₀ : ℂ, C₀ ≠ 0 ∧ ∀ (y : (UpperTheory.V.TR.Rinf F)ˣ), (∀ v, 0 < y.val v) → ∀ (yf : (Af F)ˣ) (ξ : Fˣ),
    Integrable (fun τ : IdeleGroup F => kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ))
      (ideleMeasure F) ∧
    ∫ τ, kern c (yAd y yf) τ ξ * ((ω.1 τ : ℂˣ) : ℂ)⁻¹ * ((ideleModule F τ : ℝ) : ℂ) ∂ideleMeasure F =
      C₀ * if ∀ v, 0 < reAt v (ξ : F) then
        coefAt (divS ω c) (algebraMap F (Af F) (ξ : F) * (yf : Af F)) *
          Complex.exp (-(2 * Real.pi : ℂ) * ∑ v, (reAt v (ξ : F) : ℂ) * (y.val v : ℂ))
      else 0

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.ScalarActionHolds
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne

theorem scalar_action_holds : SPois → SInt → SSmooth → SSmul := by
  intro _ _ _ F _ _ _ ω c k φ a ha
  have e2 : ∀ g, (a • φ).1 g = a * φ.1 g := fun _ => rfl
  refine ⟨fun h => ?_, fun c₀ b h => ?_⟩
  · obtain ⟨⟨hl, hlev, hk, hz, hg⟩, hlevel, hcent, hwt, hlow⟩ := h
    refine ⟨⟨fun γ g => ?_, ?_, ?_, ?_, fun g => ?_⟩, fun w => Submodule.smul_mem _ a (hlevel w),
      fun z g => ?_, fun v => ?_, fun v => ?_⟩
    · rw [e2, e2, hl]
    · have e : {x | UpperTheory.V.TR.finRep F 2 x (a • φ) = a • φ} = {x | UpperTheory.V.TR.finRep F 2 x φ = φ} := by
        ext x
        simp only [Set.mem_ofPred_eq, map_smul]
        exact smul_right_inj ha
      rw [e]
      exact hlev
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ (Set.range fun x => UpperTheory.V.TR.cptRep F 2 x φ)) (Submodule.span_le.2 ?_)
      rintro _ ⟨x, rfl⟩
      show UpperTheory.V.TR.cptRep F 2 x (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨x, rfl⟩)
    · refine Submodule.finiteDimensional_of_le
        (S₂ := Submodule.span ℂ ((fun z : Module.End ℂ (UpperTheory.V.TR.Sm F 2) => z φ) '' UpperTheory.V.TR.Zalg F 2))
        (Submodule.span_le.2 ?_)
      rintro _ ⟨z, hz', rfl⟩
      show z (a • φ) ∈ _
      rw [map_smul]
      exact Submodule.smul_mem _ a (Submodule.subset_span ⟨z, hz', rfl⟩)
    · obtain ⟨C, N, hC⟩ := hg g
      refine ⟨‖a‖ * C, N, fun y => ?_⟩
      rw [e2, norm_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hC y) (norm_nonneg a)
    · rw [e2, e2, hcent]
      ring
    · simp only [map_smul]
      rw [← smul_sub, hwt v]
      exact smul_comm _ _ _
    · simp only [map_smul]
      rw [← smul_sub, hlow v, ← smul_add]
      exact smul_comm _ _ _
  · intro x y hy yf
    have e : ∀ z : Af F, coefAt (fun 𝔪 => a * b 𝔪) z = a * coefAt b z := by
      intro z
      unfold coefAt
      split_ifs <;> simp
    convert (h x y hy yf).mul_left a using 1
    · funext ξ
      rw [e, mul_assoc]
    · rw [e2]
      simp only
      ring

end UpperTheory.HilbertEisensteinWeightOne
end
end

