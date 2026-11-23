module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvMemDoubleCosetAndComm
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0690
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryDoubleCosetFiniteLeftCosets
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0333
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
public import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnramifiedOfSphericalVectorDictionary
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0718
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.EqOfPowEqOneOfNormSubLt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0720
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0284
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSatUEigenvector
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeSatakeEigen

theorem exists_satU_eigenvector : ∀ {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))] [CompleteSpace K] (ϖ : K) (σ : K →+* K) (q n : ℕ), Formalism.UG.IsUnramInv ϖ σ q → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (T : (Formalism.UG.GU σ n → ℂ) → Module.End ℂ V), (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (h₁ + h₂) = T h₁ + T h₂) → (∀ (c : ℂ), ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (c • h) = c • T h) → T (Formalism.UG.dosetInd ℂ (Formalism.UG.KU σ n) 1) = 1 → (∀ h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), ∀ h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T (Formalism.UG.conv (Formalism.UG.KU σ n) h₁ h₂) = T h₁ * T h₂) → ∀ x₀ : V, x₀ ≠ 0 → ∃ α : Fin (n / 2) → ℂ, ∃ x : V, x ≠ 0 ∧ ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T h x = Formalism.UG.SatU ϖ q h α • x := by
  intro K _ _ _ ϖ σ q n hU V _ _ _ T hadd hsmul h1 hmul x₀ hx₀
  haveI : Nontrivial V := ⟨⟨x₀, 0, hx₀⟩⟩
  have hcomm : ∀ a b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n), T a.1 * T b.1 = T b.1 * T a.1 := by
    intro a b
    rw [← hmul _ a.2 _ b.2, ← hmul _ b.2 _ a.2, GlobalTheory.UnitarySwap.heckeCommU K ϖ σ q n ℂ hU _ a.2 _ b.2]
  obtain ⟨x, hx0, hx⟩ := GlobalTheory.exists_common_eigenvector_of_commute
    (fun b : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) => T b.1) hcomm
  choose c hc using hx
  have hinj : Function.Injective fun a : ℂ => a • x := smul_left_injective ℂ hx0
  let l : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n) →ₗ[ℂ] ℂ :=
    { toFun := c
      map_add' := fun a b => hinj (by
        show c (a + b) • x = (c a + c b) • x
        rw [← hc, add_smul, ← hc, ← hc]
        show T (a.1 + b.1) x = _
        rw [hadd _ a.2 _ b.2]; rfl)
      map_smul' := fun r a => hinj (by
        show c (r • a) • x = (r * c a) • x
        rw [← hc, mul_smul, ← hc]
        show T (r • a.1) x = _
        rw [hsmul r _ a.2]; rfl) }
  have hl1 : l ⟨_, Formalism.UG.Final.DosetIndMem _ _ ℂ 1⟩ = 1 := hinj (by
    show c _ • x = (1 : ℂ) • x
    rw [← hc, one_smul]
    show T (Formalism.UG.dosetInd ℂ _ 1) x = x
    rw [h1]; rfl)
  have hlm : ∀ f f' : Formalism.UG.Hecke ℂ (Formalism.UG.KU σ n),
      l ⟨_, Formalism.UG.Final.HeckeConvMem _ _ ℂ (Formalism.UG.P.isCommensurated_integral_unitary_of_unramified hU n) _ f.2 _ f'.2⟩ = l f * l f' :=
    fun f f' => hinj (by
      show c _ • x = (c f * c f') • x
      rw [← hc]
      show T (Formalism.UG.conv _ f.1 f'.1) x = _
      rw [hmul _ f.2 _ f'.2, Module.End.mul_apply, hc f', map_smul, hc f, smul_smul, mul_comm])
  obtain ⟨α, hα⟩ := GlobalTheory.LFun.SatCompare.exists_satU_eq hU l hl1 hlm
  refine ⟨fun i => (α i : ℂ), x, hx0, fun h hh => ?_⟩
  rw [hc ⟨h, hh⟩]
  congr 1
  exact hα ⟨h, hh⟩

end GlobalTheory.HeckeSatakeEigen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTypeComponents
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

namespace GlobalTheory.TypeRec

theorem exists_isComp_of_rowDepth {D : D7} (I : Ident D) (rep : D.what₂.FT → NG.FinTyp D.host.E D.R.r)
    (h : GlobalTheory.HeightCounting.RowDepth D rep) : ∃ cp, IsComp I rep cp := by
  have : ∀ σ k v, ∃ c : GlobalTheory.GoodTypes.LocRep D k, ∃ (s : ReciprocityTheory.Aut.SplitPlace D.host.E) (h : s.w = D.naut.plGw k v)
    (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) ((D.naut.plGw k v).adicCompletion D.host.E))),
    GlobalTheory.HeightCounting.IsLocS (rep σ).S s (h ▸ τ) ∧ c = pull I k v τ := by
    intro σ k v
    obtain ⟨s, τ, hs, h1, -⟩ := h σ k v
    have gen : ∀ (w) (e : s.w = w), ∃ τ' : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E)),
        GlobalTheory.HeightCounting.IsLocS (rep σ).S s (e ▸ τ') := by
      rintro _ rfl
      exact ⟨τ, h1⟩
    obtain ⟨τ', a⟩ := gen _ hs
    exact ⟨_, s, hs, τ', a, rfl⟩
  choose c hc using this
  exact ⟨c, hc⟩

end GlobalTheory.TypeRec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedByUnitaryIntegralPointsOfLevelFixed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped TensorProduct
open Classical

noncomputable section

namespace GlobalTheory.UnramDict

theorem fixed_of_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (U : Submodule ℂ (UA L n → ℂ)), IsAutRepU U → ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ U0 : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U0 ↔ κ ∈ Umax L n)) → ∀ (σ : w.adicCompletion L →+* w.adicCompletion L) (b : GL (Fin n) (w.adicCompletion L)), b ∈ GlobalTheory.LFun.KGL w (n := n) → ∀ p : locU n w →* Formalism.UG.GU σ n, (∀ x, (p x).val = b⁻¹ * cLoc w x.val * b) → ∀ φ ∈ U, (∀ g, ∀ κ ∈ U0, φ (F.j (g * κ)) = φ (F.j g)) → ∀ x : locU n w, p x ∈ Formalism.UG.KU σ n → RU L n x.val φ = φ := by
  intro L _ _ _ n F U hU v w hw U0 hU0 σ b hb p hp φ hφU hfix x hK
  obtain rfl : w.under (𝓞 (maximalRealSubfield L)) = v := HeightOneSpectrum.ext hw
  have hK1 : (p x).val ∈ GlobalTheory.LFun.KGL w (n := n) := (Subgroup.mem_subgroupOf.1 hK).2
  have hK2 : cLoc w x.val ∈ GlobalTheory.LFun.KGL w (n := n) := by
    have h : cLoc w x.val = b * (p x).val * b⁻¹ := by rw [hp]; group
    rw [h]
    exact mul_mem (mul_mem hb hK1) (inv_mem hb)
  have hx := x.2
  obtain ⟨y, hy⟩ := F.onto x.val (Subgroup.mem_inf.1 hx).1
  have hyU : y ∈ Umax L n := fun i j => mem_ALint F _ fun u => by
    rw [← F.loc, hy]
    exact cLoc_entry_mem hx hK2 u i j
  have hk (a : L) (z : AFplus L) :
      F.κ.toRingHom (a ⊗ₜ[maximalRealSubfield L] z) =
        algebraMap L _ a * GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
    have h1 (z : AFplus L) : F.κ (1 ⊗ₜ z) =
        GlobalTheory.AdeleBaseChange.adMap (maximalRealSubfield L) L z := by
      refine FiniteAdeleRing.ext _ fun q => ?_
      obtain ⟨i, hi, hia⟩ := F.right q (q.under (𝓞 (maximalRealSubfield L))) rfl
      rw [hia]
      change i (z (q.under (𝓞 (maximalRealSubfield L)))) = GlobalTheory.LFun.complMap rfl (z (q.under (𝓞 (maximalRealSubfield L))))
      refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield L)
        (q.under (𝓞 (maximalRealSubfield L)))).equalizer hi
        (GlobalTheory.LFun.InertChart.continuous_complMap rfl) (funext fun k => ?_)) _
      change i (algebraMap _ _ k) = GlobalTheory.LFun.complMap rfl (algebraMap _ _ k)
      rw [GlobalTheory.LFun.complMap_algebraMap]
      have he : (algebraMap (maximalRealSubfield L) (AFplus L) k) (q.under (𝓞 (maximalRealSubfield L))) =
          algebraMap _ (HeightOneSpectrum.adicCompletion (maximalRealSubfield L) (q.under (𝓞 (maximalRealSubfield L)))) k := rfl
      rw [← he, ← hia, Algebra.algebraMap_eq_smul_one (A := AFplus L) k, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one, F.left]
      rfl
    rw [← h1, ← F.left, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rfl
  have hc (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (z : AL L)
      (hz : ∀ u : HeightOneSpectrum (𝓞 L), u.under (𝓞 (maximalRealSubfield L)) = v → F.κ z u = 0) :
      compAt L v z = 0 :=
    (GlobalTheory.AdeleBaseChange.prV_eq_zero_iff (ι := F.κ.toRingHom) hk v z).2 hz
  have hyt : TrivOutside {w.under (𝓞 (maximalRealSubfield L))} y := by
    intro v hv
    refine Matrix.ext fun i j => ?_
    have h0 := hc v (y.1.val i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) fun u hu => by
      have h := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 u)
        (fun e => hv (hu.symm.trans e)))
      have h1 := F.loc y u i j
      rw [hy, h] at h1
      rw [map_sub]
      change F.κ _ u - F.κ _ u = 0
      rw [← h1]
      simp only [Units.val_one, Matrix.one_apply]
      split_ifs <;> simp <;> rfl
    rw [map_sub, sub_eq_zero] at h0
    rw [Matrix.map_apply, h0]
    simp only [Matrix.one_apply]
    split_ifs <;> simp
  have hy0 : y ∈ U0 := (hU0 y hyt).2 hyU
  rw [← sub_eq_zero]
  refine GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ (hU.aut _ (U.sub_mem (hU.stable _ _ hφU) hφU)) fun z hz => ?_
  obtain ⟨g, rfl⟩ := F.onto z hz
  change φ (F.j g * x.val) - φ (F.j g) = 0
  rw [← hy, ← map_mul, sub_eq_zero]
  exact hfix g y hy0

end GlobalTheory.UnramDict

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisCharacterEqOneOfTrivialDegreeOneFrobeniusStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.galoisCharacter_eq_one_of_trivial_degreeOne_frobenius : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime]
    (φ : G E Ω →* (Qbar l)ˣ), Continuous φ →
    (∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, w.asIdeal.inertiaDeg ℤ = 1 → w.asIdeal.ramificationIdx ℤ = 1 →
      ∀ (A : ValuationSubring Ω) (σ : G E Ω), IsPlaceOver (F := E) A w → IsFrob (F := E) A (normV w) σ → φ σ = 1) →
    φ = 1 := by
  first | exact @GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial | exact GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial | (intros; apply GlobalTheory.FrobTrivChar.eq_one_of_frob_trivial <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeCharRestrictMaxRealValEqProdAboveStatement
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open _root_.GlobalTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharRestrictMaxReal_val_eq_prod_above : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ν : Formalism.L2.Host.HChar E)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))),
    (∀ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v,
      ν.UnrAt w ∧ w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield E)) = 1) →
    (GlobalTheory.PolChar.resReal ν).val v = ∏ w ∈ Formalism.L2.Host.aboveF (L := E) (maximalRealSubfield E) v, ν.val w := by
  first | exact @GlobalTheory.PolChar.resReal_val_eq_prod | exact GlobalTheory.PolChar.resReal_val_eq_prod | (intros; apply GlobalTheory.PolChar.resReal_val_eq_prod <;> assumption)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeFunIAddSmul
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Formalism.UG

namespace GlobalTheory.InertHeckeAdd

open Classical in
theorem heckeFunI_add_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (U : Subgroup (GAf L n)), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (h₁ h₂ : Formalism.UG.GU Dv.σw n → ℂ), h₁ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → h₂ ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n) → ∀ (c : ℂ) (f : GAf L n → W), heckeFunI L n U Dv (h₁ + h₂) f = heckeFunI L n U Dv h₁ f + heckeFunI L n U Dv h₂ f ∧ heckeFunI L n U Dv (c • h₁) f = c • heckeFunI L n U Dv h₁ f := by
  intro L _ _ _ n v w Dv U hU W _ _ h h' hh hh' c f
  have hfin : ∀ k ∈ Hecke ℂ (KU Dv.σw n), Set.Finite {c : GAf L n ⧸ U | ∃ x : GAf L n,
      (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x ∧ Dv.hval k (Dv.loc x) ≠ 0} := fun k hk =>
    GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
      (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU k hk
  have hsupp : ∀ k ∈ Hecke ℂ (KU Dv.σw n), ∀ (φ : GAf L n → W) (g : GAf L n),
      (Function.support (fun c : GAf L n ⧸ U =>
        if hc : ∃ x : GAf L n, (x : GAf L n ⧸ U) = c ∧ TrivOutside {v} x then
          Dv.hval k (Dv.loc hc.choose) • φ (g * hc.choose) else 0)).Finite := by
    intro k hk φ g
    refine (hfin k hk).subset ?_
    intro c hc
    simp only [Function.mem_support] at hc
    split_ifs at hc with h1
    · refine ⟨h1.choose, h1.choose_spec.1, h1.choose_spec.2, ?_⟩
      intro h0
      rw [h0, zero_smul] at hc
      exact hc rfl
    · exact absurd rfl hc
  have hadd : ∀ y, Dv.hval (h + h') y = Dv.hval h y + Dv.hval h' y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  have hsmul : ∀ y, Dv.hval (c • h) y = c * Dv.hval h y := by
    intro y; unfold InertDatum.hval; split_ifs <;> simp
  refine ⟨?_, ?_⟩
  · funext g
    simp only [heckeFunI, Pi.add_apply]
    rw [← finsum_add_distrib (hsupp h hh f g) (hsupp h' hh' f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hadd, add_smul]
  · funext g
    simp only [heckeFunI, Pi.smul_apply]
    rw [_root_.smul_finsum' c (hsupp h hh f g)]
    refine finsum_congr fun c => ?_
    split_ifs <;> simp [hsmul, mul_smul]

end GlobalTheory.InertHeckeAdd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertLocalMemIntegralPointsOfLatticeStabilizer
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.InertKU

theorem compAt_mem_tensInt (L : Type) [Field L] [NumberField L] [IsCMField L]
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) {z : AL L} (hz : z ∈ ALint L) :
    compAt L v z ∈ Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v) := by
  have key : ALint L ≤ (Formalism.UG.tensInt (F := maximalRealSubfield L)
      (v.adicCompletion (maximalRealSubfield L)) (Formalism.UG.intOE L)
      (Formalism.UG.Ov (maximalRealSubfield L) v)).comap (compAt L v) := by
    rw [ALint, Subring.closure_le]
    rintro _ (⟨y, rfl⟩ | ⟨a, ha, rfl⟩)
    · apply Subring.subset_closure
      left
      refine ⟨⟨(y : L), y, rfl⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
      rfl
    · apply Subring.subset_closure
      right
      refine ⟨⟨a v, ha v⟩, ?_⟩
      rw [GlobalTheory.InertUmax.compAt_tmul]
  exact key hz

theorem mem_range_bc_of_entries {K : Type} [Field K] (S : Subring K) {n : ℕ} (g : GL (Fin n) K)
    (hg : ∀ i j, (g : Matrix (Fin n) (Fin n) K) i j ∈ S)
    (hg' : ∀ i j, ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j ∈ S) :
    g ∈ (Formalism.UG.bc (n := Fin n) S.subtype).range := by
  let M : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg i j⟩
  let M' : Matrix (Fin n) (Fin n) S := fun i j => ⟨_, hg' i j⟩
  have hM : (RingHom.mapMatrix S.subtype) M = (g : Matrix (Fin n) (Fin n) K) := rfl
  have hM' : (RingHom.mapMatrix S.subtype) M' = ((g⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := rfl
  have inj : Function.Injective (RingHom.mapMatrix (m := Fin n) S.subtype) := by
    intro A B h
    ext i j
    exact congrFun (congrFun h i) j
  have h1 : M * M' = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.mul_inv g)
  have h2 : M' * M = 1 := inj (by rw [map_mul, map_one, hM, hM']; exact Units.inv_mul g)
  refine ⟨⟨M, M', h1, h2⟩, ?_⟩
  ext i j
  rfl

theorem loc_inv (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (x : GAf L n) : Dv.loc x⁻¹ = (Dv.loc x)⁻¹ := by
  unfold InertDatum.loc
  simp only [InvMemClass.coe_inv, map_inv]
  group

theorem loc_entries_mem (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L))
    (Dv : InertDatum L n v w) (y : GAf L n) (hy : y ∈ Umax L n) (i j : Fin n) :
    ((Dv.loc y : GL (Fin n) (w.adicCompletion L)) : Matrix (Fin n) (Fin n) (w.adicCompletion L)) i j
      ∈ Formalism.UG.intL (w.adicCompletion L) := by
  have hP := GlobalTheory.InertUmax.entries_mem_of_range _ _ Dv.Pint
  have hP' := GlobalTheory.InertUmax.entries_mem_of_range _ _ (inv_mem Dv.Pint)
  have hE : ∀ l k, ((Formalism.UG.bc (n := Fin n)
      (Dv.e : L ⊗[maximalRealSubfield L] v.adicCompletion (maximalRealSubfield L) →+* w.adicCompletion L)
      (Matrix.GeneralLinearGroup.map (compAt L v) (y : GL (Fin n) (AL L))) : GL (Fin n) _) :
        Matrix (Fin n) (Fin n) (w.adicCompletion L)) l k ∈ Formalism.UG.intL (w.adicCompletion L) :=
    fun l k => (Dv.integ _).1 (compAt_mem_tensInt L v (hy l k))
  unfold InertDatum.loc
  simp only [Units.val_mul, Matrix.mul_apply]
  exact Subring.sum_mem _ fun k _ => Subring.mul_mem _
    (Subring.sum_mem _ fun l _ => Subring.mul_mem _ (hP' i l) (hE l k)) (hP k j)

theorem loc_mem_KU : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (x : GAf L n), x ∈ Umax L n → ∀ hg : Dv.loc x ∈ Formalism.UG.GU Dv.σw n, (⟨Dv.loc x, hg⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n := by
  intro L _ _ _ n v w Dv x hx hg
  rw [Formalism.UG.KU, Subgroup.mem_subgroupOf]
  refine ⟨hg, ?_⟩
  apply mem_range_bc_of_entries
  · exact loc_entries_mem L n v w Dv x hx
  · intro i j
    rw [← loc_inv]
    exact loc_entries_mem L n v w Dv x⁻¹ (inv_mem hx) i j

end GlobalTheory.InertKU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IntegralCombIdempotentSectionsNonnegOverPlace
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IdemInt

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke.UnusedSlot39

section Val

variable {K : Type} [Field K] [NumberField K] {R : Type} [CommRing R] [Algebra K R]
  {la : HeightOneSpectrum (𝓞 K)} {u : R → EReal}

theorem nonneg_of_idem (hu : IsVal la u) {x : R} (hx : x * x = x) : 0 ≤ u x := by
  have h := hu.mul x x
  rw [hx] at h
  rcases eq_or_ne (u x) ⊤ with h0 | h0
  · rw [h0]
    exact le_top
  · have hr : (((u x).toReal : ℝ) : EReal) = u x := EReal.coe_toReal h0 (hu.ne_bot x)
    rw [← hr] at h ⊢
    rw [← EReal.coe_add, EReal.coe_eq_coe_iff] at h
    exact EReal.coe_nonneg.mpr (by linarith)

theorem nonneg_smul (hu : IsVal la u) {a : K} (ha : la.valuation K a ≤ 1) {x : R} (hx : 0 ≤ u x) :
    0 ≤ u (a • x) := by
  rcases eq_or_ne a 0 with rfl | ha0
  · rw [zero_smul, hu.zero]
    exact le_top
  · rw [hu.smul a x ha0]
    have hv0 : la.valuation K a ≠ 0 := (Valuation.ne_zero_iff _).mpr ha0
    have hlog : (la.valuation K a).log ≤ 0 := by
      rw [WithZero.log_le_iff_le_exp hv0, WithZero.exp_zero]
      exact ha
    refine add_nonneg ?_ hx
    unfold Formalism.BasicNotions.vAdd
    have hn : (0 : ℤ) ≤ -(la.valuation K a).log := neg_nonneg.mpr hlog
    exact_mod_cast hn

theorem nonneg_sum (hu : IsVal la u) {ι : Type} (s : Finset ι) (x : ι → R) (hx : ∀ i ∈ s, 0 ≤ u (x i)) :
    0 ≤ u (∑ i ∈ s, x i) := by
  refine Finset.sum_induction x (fun y => 0 ≤ u y) (fun a b ha hb => ?_) ?_ hx
  · exact le_trans (le_min ha hb) (hu.add a b)
  · show (0 : EReal) ≤ u 0
    rw [hu.zero]
    exact le_top

end Val

theorem idem_comb_mul_nonneg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (la : HeightOneSpectrum (𝓞 c.F)) (m : ℕ) (χ : Fin m → Rul Xo c) (v : Fin m → c.F), (∀ i, χ i ∈ sec Xo c 0 0 ∧ χ i * χ i = χ i) → (∀ i, la.valuation c.F (v i) ≤ 1) → ∀ f : Rul Xo c, (∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u f) → ∀ u ∈ valSet Xo c (algCls Xo c) la, 0 ≤ u ((∑ i, v i • χ i) * f) := by
  intro E _ _ _ H Dw l Xo c la m χ v hχ hv f hf u hu
  have hV : IsVal la u := isVal_valSet la u hu
  have h1 : 0 ≤ u (∑ i, v i • χ i) :=
    nonneg_sum hV Finset.univ _ fun i _ => nonneg_smul hV (hv i) (nonneg_of_idem hV (hχ i).2)
  rw [hV.mul]
  exact add_nonneg h1 (hf u hu)

end GlobalTheory.IdemInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionGLSurjective
section
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.GLp.reduction_GL_surjective : ∀ (g : ℕ) [Fact g.Prime] (n : ℕ), Function.Surjective (GlobalTheory.GLp.red g n) :=
  fun g _ n => GlobalTheory.GLp.red_surjective g n
end

