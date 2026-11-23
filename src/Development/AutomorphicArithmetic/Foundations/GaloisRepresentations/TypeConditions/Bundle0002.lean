module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0734
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.GoodRCongr
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SplitBCOfGalIso
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0600
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0685
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0549
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0598
public import Mathlib
public import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0079
public import Development.DiscreteGroups.GlobalIrreducibility.Bundle0014
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0485
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0520
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0541
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0268
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0288
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0700
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepthZeroLabelsOfLabelLaws
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0453
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0505
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0317
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0583
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.SpanMulMem

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CompatR
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PointRepAboveL

noncomputable section

namespace UpperTheory.GalS

theorem compatR (D : D7) (h0 : SumRepresentations.tie0 D) (h2 : AutomorphicGaloisAdmissible D.nd D.naut) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc)
    (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (P : D.naut.AV i) (Pa : List (Formalism.BasicNotions.Part D.naut.CG)) (hP : D.naut.ptV i P = some x)
    (hB : IsBCV D.nd D.naut i P Pa) (w : PlE D.host) (hw : w ∈ placesOver D.host.E (D.nd.l i))
    (hn : Nc D.nd D.naut (isoLoc D.nd D.naut Pa w)) :
    D.naut.IsdRW i (mapRep (iotaOQ D.nd D.naut i) (r x)) w ∧
    UpperTheory.GalN.RelA D.nd D.naut (D.naut.wdOf i (mapRep (iotaOQ D.nd D.naut i) (r x)) w)
      (D.naut.lpTw (isoLoc D.nd D.naut Pa w) ((1 - (D.R.nV : ℝ)) / 2)) ∧
    ∀ τ, InducesW D.nd i τ w →
      D.naut.jumpsW i (mapRep (iotaOQ D.nd D.naut i) (r x)) τ = D.naut.locAutHodgeTateWeightsLevelZero i τ := by
  obtain ⟨ρ, hc, hs, hwd, hl⟩ := isoRep D h0 h2 i P Pa hB
  obtain ⟨Pm, hPm⟩ := rep_conj D h5 i r hr x P Pa hP hB ρ hc hs hwd
  obtain ⟨-, hconj, -, -⟩ := h0.2.2.2.2.2 i
  obtain ⟨hdR, hWD, hJ⟩ := hconj _ ρ _ hc Pm hPm
  refine ⟨(hdR w hw).2 (hl w hw hn).1, ?_, fun τ hτ => ?_⟩
  · rw [hWD w (Or.inr (hl w hw hn).1)]
    exact (hl w hw hn).2.1
  · rw [hJ τ (fun w' h' => by rw [place_unique hτ h']; exact (hl w hw hn).1)]
    exact (hl w hw hn).2.2 τ hτ

end UpperTheory.GalS

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.JointConditionOfConstituentConditionSplit
section
noncomputable section

section
open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal

theorem UpperTheory.GalS.jointCondition_of_constituentCondition_split (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (h : UpperTheory.GalS.DistinctAbsIrredConstituents D.nd i r) (hS : GlobalTheory.SplitCoef.OSplitAt D i) : AbsIrreducibleDistinct D i r := by
  obtain ⟨K', hK', hA, _, hK⟩ := h
  exact _root_.GlobalTheory.absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct D i r hS hr K' (algebraMap (Kf D.nd i) K') (fun x => (hK x).2)
end

section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal
namespace GlobalTheory.CrysFromGTwo

end GlobalTheory.CrysFromGTwo
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.DualTwistCrys

end GlobalTheory.DualTwistCrys
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module
namespace GlobalTheory.CrysChiOne
variable {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
  {hw : w ∈ placesOver D.host.E (D.nd.l i)}

end GlobalTheory.CrysChiOne
end

section
namespace Formalism.MainNotions.N
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open NumberField IsDedekindDomain

end Formalism.MainNotions.N
end

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices
namespace GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

end GlobalTheory.AbsoluteIrreducibilityOfTraceSpan
end

section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameAnyAtOfIsConjPl
section
noncomputable section

namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem ineAt' : ∀ D : D7, UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (k : Fin 2) (v : D.nd.PlG k) (w), w = D.naut.plGw k v → w ∉ placesOver D.host.E (D.nd.l i) → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map (iotaO D.nd D.naut i) = D.naut.inePol (D.naut.locG π w) s := by
  intro D hG hF i π ρ hc ha hfull hρ k v w hwv hw s hs
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) := by
    have := hfull.2 k v
    rwa [isoLoc_cusp, ← hwv] at this
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    simp only [Ranks.r]
    omega
  obtain ⟨r, hrc, hr⟩ := hG i D.R.r hr1 π hc ha
  obtain ⟨hιc, -⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  obtain ⟨hρc, -, hρf⟩ := hρ
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have hinj : Function.Injective (Polynomial.map (D.naut.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (D.naut.iotaQC i).injective
  have hfin := placesOver_finite_of_prime D.host.E (D.nd.lPrime i).out
  have hall := (hfin.eventually_cofinite_notMem.and (D.naut.locG_unr_ae π)).and hρf
  have hd := hF _ (Filter.eventually_cofinite.1 hall)
  have key := GlobalTheory.TypeLeaf.charpoly_eq_of_dense _ (Qbar (D.nd.l i)) D.R.r
    (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i))
    (fun g => ((r g : GL (Fin D.R.r) (Qbar (D.nd.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))))
    _ hd (hρc.matrix_map hιc) hrc (by
      rintro g ⟨v, hv, -, B, hB, hg⟩
      obtain ⟨⟨h1, h2⟩, h3⟩ := not_not.1 hv
      apply hinj
      have hu : D.naut.unr (D.naut.wdOf i r v) := by
        rw [(hr v h1).eq_of_unr ((D.naut.unr_tw _ _).2 h2)]; exact (D.naut.unr_tw _ _).2 h2
      rw [Matrix.charpoly_map, Polynomial.map_map, ← hcomp, h3 B g hB hg, isoLoc_cusp,
        D.naut.wdOf_frob i r v h1 hrc hu B g hB hg, (hr v h1).eq_of_unr ((D.naut.unr_tw _ _).2 h2)]
      rfl) s
  rw [hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map, key, D.naut.wdOf_ine i r w hw hrc s hs, (hr w hw).ine ((UpperTheory.GalS.nc_tw _ _).2 hn) s hs,
    D.naut.inePol_tw _ _ _ hs]

end GlobalTheory.IneAway

namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

end GlobalTheory.TypeLeaf

namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise

end GlobalTheory.TypeLeaf.ConjPlace

namespace GlobalTheory.AdmTame
open NumberField IsDedekindDomain _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem galAwayOfS' {D : D7} (hG : UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut) : UpperTheory.GalS.GalAwayN D := fun i a ha π hc hr => by
  obtain ⟨ρ, hρc, -, hρw, -⟩ := (hG i).1 a ha π hc hr
  exact ⟨ρ, hρc, hρw⟩

end GlobalTheory.AdmTame
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TameGeneratorResidual
section
noncomputable section

namespace GlobalTheory.ResidualTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem cpAt' : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → GlobalTheory.RowTie.IotaRed D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩; haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩; Matrix.charpoly ((D.ntypes.rbar σ (D.nd.w i) (D.ntypes.tg k v) : GL (Fin D.R.r) _) : Matrix (Fin D.R.r) (Fin D.R.r) _) = ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.iota k v (D.nd.w i) (Formalism.CyclotomicNorms.primeToPart (D.what₂.places.resChar (D.nd.w i)) x))).prod := by
  intro D hT hI hL hR σ k v i hl hocc hgood
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hW⟩ := hR i σ hocc hgood
  obtain ⟨B, κ, h1, h2⟩ := hI i
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (k := k) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, -⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have h := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rwa [(hW k v hl).dim, D.naut.lpDim_tw] at h
  have hfull : (D.naut.items₂ k _ (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2)) :=
    (UpperTheory.GalS.nc_tw _ _).2 (hL.2 k v _ hfull (by rw [← D.naut.lab_loc i k σ v]; exact (hgood k).1.2.1 v)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by rw [hdim]; unfold Ranks.nV; omega)))
  have hine : ((ρ (D.ntypes.tg k v) : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map
        (iotaO D.nd D.naut i) =
      ((Formalism.CyclotomicNorms.rootsBar (D.nd.lab k σ v)).map fun x => X - C (D.ntypes.teichC k x)).prod := by
    have e := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont _ (D.ntypes.tg_mem k v)
    rw [(hW k v hl).ine hn _ (D.ntypes.tg_mem k v), D.naut.inePol_tw _ _ _ (D.ntypes.tg_mem k v), D.ntypes.inertiaCharpoly_type k v _ hfull,
      ← D.naut.lab_loc i k σ v] at e
    rw [hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact e
  have hred := GlobalTheory.TypeLeaf.map_eq_prod_of_valuationSubring B (iotaO D.nd D.naut i)
    (((fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom.comp
      κ.toRingHom).comp (IsLocalRing.residue B))
    ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) h1 (D.ntypes.teichC k)
    (fun x => fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
      (D.ntypes.iota k v (D.nd.w i) x))
    (fun x => by
      obtain ⟨h, e⟩ := h2 k v x
      exact ⟨h, congrArg (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out) e⟩)
    _ _ hine
  rw [← hT.2 i σ hocc hgood Sig ρ hP hρ (D.ntypes.tg k v)] at hred
  apply Polynomial.map_injective
    (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
    (RingHom.injective _)
  rw [hred, Polynomial.map_multiset_prod, Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun x _ => ?_)
  simp [GlobalTheory.TypeLeaf.map_primeToPart_fbar]

end GlobalTheory.ResidualTame

namespace GlobalTheory.RowWildTame
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem main_alt : ∀ (D : D7), GlobalTheory.RowCopy.RbarTie D → UpperTheory.GalS.LabTameS D.nd D.naut → UpperTheory.GalS.RowRepAtGN D → ∀ (σ : D.what₂.FT) (k : Fin 2) (v : D.nd.PlG k) (i : D.nd.Loc), D.nd.l i ≠ D.host.g k → D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 (D.naut.plGw k v)), s ∈ wildSet D.nd (D.nd.plOm.1 (D.naut.plGw k v)) → D.ntypes.rbar σ (D.nd.w i) s = 1 := by
  intro D hT hL hR σ k v i hl hocc hgood s hs hwild
  haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
  obtain ⟨Sig, ρ, hP, hρ, hc⟩ := hR i σ hocc hgood
  have hw := GlobalTheory.TameLabels.not_mem_of_ne (D := D) (v := v) (D.nd.lPrime i).out hl
  obtain ⟨hιc, hιi⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  have hcont : Continuous (fun g => ((mapRep (iotaOQ D.nd D.naut i) ρ g : GL (Fin D.R.r) (Qbar (D.nd.l i))) :
      Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i)))) := hρ.1.matrix_map hιc
  have e := hc k v hl
  have hdim : D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) = D.R.r := by
    have := D.naut.wdOf_dim i (mapRep (iotaOQ D.nd D.naut i) ρ) (D.naut.plGw k v)
    rw [e.dim, D.naut.lpDim_tw] at this
    exact this
  have hfull : (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locW i σ (D.naut.plGw k v))).natDegree =
      D.naut.lpDim (D.naut.locW i σ (D.naut.plGw k v)) := by
    rw [← D.naut.lab_loc i k σ v, (D.nd.lab_monic k σ v).2, hdim]
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.lpTw (D.naut.locW i σ (D.naut.plGw k v)) ((1 - (D.R.r : ℝ)) / 2)) :=
    (UpperTheory.GalS.nc_tw _ _).2 (hL.2 k v _ hfull (by rw [← D.naut.lab_loc i k σ v]; exact (hgood k).1.2.1 v)
      (DiscreteGroups.sglob.DzType.big_of_le_nV D k (by rw [hdim]; unfold Ranks.nV; omega)))
  have h1 := hL.1 k v _ hfull s hs hwild
  rw [hdim] at h1
  have h2 := D.naut.wdOf_ine i (mapRep (iotaOQ D.nd D.naut i) ρ) _ hw hcont s hs
  rw [e.ine hn s hs, D.naut.inePol_tw _ _ _ hs, h1] at h2
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have h3 : ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly = (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective (iotaO D.nd D.naut i)
      ((D.naut.iotaQC i).injective.comp hιi)
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one, hcomp,
      ← Polynomial.map_map, ← Matrix.charpoly_map]
    exact h2
  have h4 := hT.2 i σ hocc hgood Sig ρ hP hρ s
  rw [h3, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one] at h4
  have h5 : ((D.ntypes.rbar σ (D.nd.w i) s : GL (Fin D.R.r) (Fb (D.what₂.places.resChar (D.nd.w i))
      (D.what₂.places.resChar_prime (D.nd.w i)))) : Matrix (Fin D.R.r) (Fin D.R.r)
      (Fb (D.what₂.places.resChar (D.nd.w i)) (D.what₂.places.resChar_prime (D.nd.w i)))).charpoly =
      (X - 1) ^ D.R.r := by
    apply Polynomial.map_injective
      (fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out).toRingHom
      (RingHom.injective _)
    rw [h4, Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_one]
  have h6 : s ∈ (D.ntypes.rbar σ (D.nd.w i)).ker := by
    refine GlobalTheory.mem_of_wild_of_pow_mem_open_normal _ _ _ _ (D.nd.plOm.2 (D.naut.plGw k v)) _ inferInstance
      (D.ntypes.rbar_open σ _) s ((D.what₂.places.resChar (D.nd.w i)) ^ D.R.r) (fun hmem => hw ?_) hwild ?_
    · rw [Nat.cast_pow, D.nd.w_l i] at hmem
      exact (D.naut.plGw k v).isPrime.mem_of_pow_mem _ hmem
    · rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
      exact GlobalTheory.TameLabels.pow_eq_one_of_charpoly _ h5
  exact h6

end GlobalTheory.RowWildTame

namespace GlobalTheory.RowTie
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

end GlobalTheory.RowTie
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.TraceOfCharpoly
section
noncomputable section

namespace UpperTheory.GalS

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

open GlobalTheory.IndefiniteRowSideFullHecke.CongruenceModuleMatrices GlobalTheory.AbsoluteIrreducibilityOfTraceSpan

theorem cyc_onto (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) (u : ℤ_[D.nd.l i]ˣ) :
    ∃ g : GE D.nd, cycZ (F := D.host.E) (Ω := D.nd.Om) (D.nd.l i) g = u := by
  haveI : IsAlgClosed D.nd.Om := IsAlgClosure.isAlgClosed D.host.E
  obtain ⟨w, hw⟩ := GlobalTheory.OChoose.placesOver_nonempty D.host.E (D.nd.l i) (D.nd.lPrime i).out
  have h1 : (D.nbr i w hw).Kw.1 = ⊥ := IntermediateField.finrank_eq_one_iff.1 ((GlobalTheory.TypeDegOne.degree_one D i k hl).2 w hw)
  obtain ⟨σ, -, hσu⟩ := GlobalTheory.Cyc.exists_inertia_cycZ_eq (D.nd.l i) u
  have hσ : σ ∈ Formalism.BasicNotions.Loc.GK (D.nbr i w hw).Kw := by
    refine GlobalTheory.EpsInertia.mem_GK _ σ fun x => ?_
    have hx := (D.nbr i w hw).j_E x
    rw [h1, IntermediateField.mem_bot] at hx
    obtain ⟨q, hq⟩ := hx
    rw [← hq]; exact σ.commutes q
  refine ⟨((D.nbr i w hw).e.symm ⟨σ, hσ⟩).1, ?_⟩
  rw [GlobalTheory.EpsInertia.cycZ_bridge (D.nbr i w hw), MulEquiv.apply_symm_apply]
  exact hσu

theorem charP_res (D : D7) (i : D.nd.Loc) : CharP (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i) := by
  have hm := Ideal.isMaximal_under_of_isIntegral_of_isMaximal (R := ℤ_[D.nd.l i]) (IsLocalRing.maximalIdeal (D.nd.O i))
  change ((IsLocalRing.maximalIdeal (D.nd.O i)).comap (algebraMap ℤ_[D.nd.l i] (D.nd.O i))).IsMaximal at hm
  have h1 : ((D.nd.l i : ℕ) : ℤ_[D.nd.l i]) ∈ (IsLocalRing.maximalIdeal (D.nd.O i)).comap (algebraMap ℤ_[D.nd.l i] (D.nd.O i)) := by
    rw [IsLocalRing.eq_maximalIdeal hm]
    exact PadicInt.irreducible_p.not_isUnit
  rw [Ideal.mem_comap, map_natCast, ← IsLocalRing.residue_eq_zero_iff, map_natCast] at h1
  exact (CharP.charP_iff_prime_eq_zero (D.nd.lPrime i).out).2 h1

def chiBar (D : D7) (i : D.nd.Loc) (j : Fin D.R.t) : GE D.nd →* IsLocalRing.ResidueField (D.nd.O i) :=
  (IsLocalRing.residue (D.nd.O i)).toMonoidHom.comp ((Units.coeHom _).comp (D.nd.chi i ((j : ℕ) + 1)))

theorem chiBar_inj (D : D7) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k) : Function.Injective (chiBar D i) := by
  intro j j' e
  haveI := charP_res D i
  have hp : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hbig : 16 * D.R.t ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k (by unfold Ranks.nV; omega)
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod (D.nd.l i))ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hζ
  have hu : IsUnit (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (ZMod.val_coe_unit_coprime ζ).symm
  obtain ⟨g, hg⟩ := cyc_onto D i k hl hu.unit
  let φ : (ZMod (D.nd.l i))ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ :=
    Units.map (ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i))).toMonoidHom
  have hφ : Function.Injective φ := Units.map_injective (RingHom.injective _)
  let R : (D.nd.O i)ˣ →* (IsLocalRing.ResidueField (D.nd.O i))ˣ := Units.map (IsLocalRing.residue (D.nd.O i)).toMonoidHom
  have hy : R (Units.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i)).toMonoidHom hu.unit) = φ ζ := by
    apply Units.ext
    show IsLocalRing.residue _ (algebraMap ℤ_[D.nd.l i] (D.nd.O i) (((ζ : ZMod (D.nd.l i)).val : ℕ) : ℤ_[D.nd.l i])) =
      ZMod.castHom (dvd_refl _) (IsLocalRing.ResidueField (D.nd.O i)) (ζ : ZMod (D.nd.l i))
    rw [map_natCast, map_natCast]
    conv_rhs => rw [← ZMod.natCast_zmod_val (ζ : ZMod (D.nd.l i)), map_natCast]
  have key : ∀ c : Fin D.R.t, R (D.nd.chi i ((c : ℕ) + 1) g) = R (D.nd.chi i 1 g) * (φ ζ ^ (c : ℕ))⁻¹ := fun c => by
    rw [D.nd.chi_def i ((c : ℕ) + 1) (by omega) (by omega), MonoidHom.mul_apply, map_mul, MonoidHom.zpow_apply,
      MonoidHom.comp_apply, hg, map_zpow, hy, ← zpow_natCast, ← zpow_neg]
    congr 2
    push_cast; ring
  have e1 : R (D.nd.chi i ((j : ℕ) + 1) g) = R (D.nd.chi i ((j' : ℕ) + 1) g) := Units.ext (DFunLike.congr_fun e g)
  rw [key, key, mul_right_inj, inv_inj, ← map_pow, ← map_pow] at e1
  have hj := j.2
  have hj' := j'.2
  exact Fin.ext (pow_injOn_Iio_orderOf (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega)
    (by rw [Set.mem_Iio, hζ]; have : D.R.t ≤ D.R.t ^ 2 := Nat.le_self_pow two_ne_zero _; omega) (hφ e1))

theorem trace_of_charpoly {k : Type} [Field k] {a t : ℕ} (M : Matrix (Fin (a + t)) (Fin (a + t)) k) (A : Matrix (Fin a) (Fin a) k)
    (c : Fin t → k) (h : M.charpoly = A.charpoly * ∏ j, (X - C (c j))) : M.trace = A.trace + ∑ j, c j := by
  have e : M.charpoly = (Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 (Matrix.diagonal c))).charpoly := by
    rw [h, Matrix.charpoly_reindex, Matrix.charpoly_fromBlocks_zero₁₂, Matrix.charpoly_diagonal]
  rw [Matrix.trace_eq_neg_charpoly_nextCoeff, e, ← Matrix.trace_eq_neg_charpoly_nextCoeff]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem trace_sumRep {k Γ : Type} [CommRing k] [Group Γ] {a b : ℕ} (ρ : Γ →* GL (Fin a) k) (ρ' : Γ →* GL (Fin b) k) (g : Γ) :
    ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k).trace =
      (ρ g : Matrix (Fin a) (Fin a) k).trace + (ρ' g : Matrix (Fin b) (Fin b) k).trace := by
  have e : ((SumRepresentations.At.sumRep ρ ρ' g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (ρ g : Matrix (Fin a) (Fin a) k) 0 0 (ρ' g : Matrix (Fin b) (Fin b) k)) := rfl
  rw [e]
  simp [Matrix.trace, Fin.sum_univ_add]

theorem noDouble_of_live (D : D7) (h5 : SumRepresentations.adm5 D) (i : D.nd.Loc) (k : Fin 2) (hl : D.nd.l i = D.host.g k)
    (hL : GlobalTheory.CoefDuty.Live D.nd i) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r)
    (hb : ResidualCharpolyIndependent D.nd i r) (x : D.nd.X i) {K' : Type} [Field K'] (f : D.nd.O i →+* K') (hf : Function.Injective f) {d u : ℕ}
    (σ : GE D.nd →* GL (Fin d) K') (υ : GE D.nd →* GL (Fin u) K') (h : d + d + u = D.R.nV) (Pm : GL (Fin D.R.nV) K')
    (hd : 0 < d)
    (hrel : ∀ g, ((Pm⁻¹ * mapRep f (r x) g * Pm : GL (Fin D.R.nV) K') : Matrix (Fin D.R.nV) (Fin D.R.nV) K') =
      Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')) : False := by
  classical
  obtain ⟨π, -, r0, ρ0, hr0, ⟨e0, he0⟩, habs⟩ := hL
  haveI := charP_res D i
  have hbig : 16 * D.R.nV ^ 2 < D.nd.l i := hl ▸ DiscreteGroups.sglob.DzType.big_of_le_nV D k le_rfl
  have hn : D.R.nV = D.R.r + D.R.t := rfl
  have hr2 : 2 ≤ D.R.r := by have := D.R.two_le_m; have := D.R.m_add_three_le_k; unfold Ranks.r; omega
  refine Dbl.core f hf (IsLocalRing.residue (D.nd.O i)) IsLocalRing.residue_surjective (a := D.R.r) (t := D.R.t) hr2
    (d := d) (u := u) (by omega) ((Units.coeHom _).comp (r x)) ((Units.coeHom _).comp σ) ((Units.coeHom _).comp υ)
    ((Units.coeHom _).comp (mapRep (IsLocalRing.residue (D.nd.O i)) ρ0)) (chiBar D i) (chiBar_inj D i k hl)
    (GlobalTheory.BurnsideField.span_mat_eq_top_of_absIrrSub _ habs) (fun g => ?_) (fun g => ?_) (fun c => ((c : ℕ) : _)) fun c c' e => ?_
  · have t := congrArg Matrix.trace (hrel g)
    rw [Units.val_mul, Units.val_mul, Matrix.trace_mul_cycle, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul] at t
    have t2 : (Matrix.reindex (finCongr h) (finCongr h) ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K')).trace = ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K').trace :=
      Equiv.sum_comp (finCongr h).symm fun j => ((SumRepresentations.At.sumRep (SumRepresentations.At.sumRep σ σ) υ g : GL (Fin (d + d + u)) K') :
        Matrix (Fin (d + d + u)) (Fin (d + d + u)) K') j j
    rw [t2, trace_sumRep, trace_sumRep, ← two_mul] at t
    exact (map_sum f _ _).trans t
  · have d0 := charpoly_of_decomp D i (fun _ => r0) (fun _ => ρ0) π ⟨e0, he0⟩ g
    have hc := charpoly_eq_of_isHeckeGalois GlobalTheory.Published.cheb_holds D i r hr π r0 hr0 g
    have e0' : (mat r0 g).charpoly = (mat ρ0 g).charpoly *
      ∏ c ∈ Finset.Icc 1 D.R.t, (X - C ((chiU D.nd i c g : (D.nd.O i)ˣ) : D.nd.O i)) := d0
    have e1 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat (r π) g).map (IsLocalRing.residue (D.nd.O i))).charpoly := hb x π g
    have e2 : ((mat (r x) g).map (IsLocalRing.residue (D.nd.O i))).charpoly =
        ((mat ρ0 g).map (IsLocalRing.residue (D.nd.O i))).charpoly * ∏ j : Fin D.R.t, (X - C (chiBar D i j g)) := by
      rw [e1, Matrix.charpoly_map, hc, e0', Polynomial.map_mul, ← Matrix.charpoly_map, Polynomial.map_prod]
      congr 1
      rw [← Finset.Ico_add_one_right_eq_Icc, Finset.prod_Ico_eq_prod_range, Nat.add_sub_cancel, Finset.prod_range]
      refine Finset.prod_congr rfl fun j _ => ?_
      rw [Polynomial.map_sub, map_X, map_C, add_comm 1]
      rfl
    exact (map_sum (IsLocalRing.residue (D.nd.O i)) _ _).trans (trace_of_charpoly (a := D.R.r) (t := D.R.t) _ _ _ e2)
  · have h1 := c.2
    have h2 := c'.2
    have h3 : D.R.nV ≤ D.R.nV ^ 2 := Nat.le_self_pow two_ne_zero _
    exact Fin.ext (CharP.natCast_injOn_Iio (IsLocalRing.ResidueField (D.nd.O i)) (D.nd.l i)
      (by rw [Set.mem_Iio]; omega) (by rw [Set.mem_Iio]; omega) e)

end UpperTheory.GalS
end
end

