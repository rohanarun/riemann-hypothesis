module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0004
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1287
public import Development.WeilBound.CoreStatements.AutomorphicKernels.TemperedUnitNorm.NormEqOneOfTemperedRec
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.TemperedOfTrueCuspidal
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0810
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0811
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff

@[expose] public section

noncomputable section

namespace UpperTheory.GalS
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.WeilDeligne

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)

def Gw {w : PlE H} (y : A.LP w) : Prop := A.unr y ∨ (thr w (A.lpDim y) = 2 ∧ Sep N A y)

variable {N A}
theorem Gw.nc (T : GlobalTheory.RowTie.WDTie N A) {w : PlE H} {y : A.LP w} (h : Gw N A y) : Nc N A y := by
  refine h.elim Nc.of_unr fun ⟨ht, hs⟩ => ?_
  obtain ⟨htame, σ, hσ, hsep⟩ := hs
  have hwd : SepW (T.e w y) := by
    refine ⟨(WD.tame_iff_inePol _).2 ?_, σ, hσ, ?_⟩
    · intro γ hγ
      have hI := GlobalTheory.TameEig.wild_mem_Ine (N.plOm.1 w) γ hγ
      rw [← T.inePol w y γ hI, T.dim]
      exact htame γ hI hγ
    · rwa [← T.inePol w y σ hσ]
  have hn := hwd.ncW (by rwa [T.dim])
  refine ⟨htame, (T.mono0 w y).2 hn.2.1, ?_⟩
  intro γ hγ z hz
  exact hn.2.2 γ hγ.1 hγ.2 z (by rwa [← T.inePol w y γ hγ.1, T.dim])
end

section
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

theorem NcW.congr {x y : WD h} (k : NcW x) (d : y.lpDim = x.lpDim) (m : x.mono0 → y.mono0)
    (e : ∀ σ ∈ Ine (F := E) B, y.inePol σ = x.inePol σ) : NcW y :=
  ⟨fun σ hσ => by rw [e σ (GlobalTheory.TameEig.wild_mem_Ine B σ hσ), d]; exact k.1 σ hσ, m k.2.1,
    fun γ hγ hc z hz => k.2.2 γ hγ hc z (by rwa [← e γ hγ, ← d])⟩

theorem NcW.char {x c : WD h} (k : NcW x) (hc : c.lpDim = 1) (hu : c.unr) : NcW (x.lpChar c) := by
  refine k.congr ?_ (WD.monomial_char_iff _ _ hc).2 fun σ hσ => ?_
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    obtain ⟨n', b, rfl⟩ := c.exists_rep
    rw [WD.lpDim_mk] at hc
    rw [WD.lpChar_mk, WD.lpDim_mk, WD.lpDim_mk, Module.finrank_tensorProduct, hc, mul_one]
  · rw [GlobalTheory.RowTieLP.inePol_char hc hσ (z := 1) (by rw [inePol_of_unr hu hσ, hc]; simp), scaleRoots_one]

theorem NcW.tw {x : WD h} (k : NcW x) (s : ℝ) : NcW (x.lpTw s) := by
  refine k.congr ?_ (WD.monomial_twist_iff _ _).2 fun σ hσ => ?_
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    rw [WD.lpTw_mk, WD.lpDim_mk, WD.lpDim_mk]
  · obtain ⟨n, a, rfl⟩ := x.exists_rep
    rw [WD.lpTw_mk, WD.inePol_of_mem_Ine _ hσ, WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.charPol_mk, WDRep.tw_ρ,
      deg_ineIncl]
    simp
end
end UpperTheory.GalS

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.RowTie (WDTie)
open GlobalTheory.Pst GlobalTheory.GalOfCusp

variable (D : D7) (T : WDTie D.nd D.naut) {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
  (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))

def _root_.UpperTheory.GalS.IsGaloisRepOfN (D : D7) {a : ℕ} (π : D.naut.CG a) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)
    (r : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧
  IsSSRep r ∧
  ∀ w : PlE D.host, w ∉ placesOver D.host.E l →
    (UpperTheory.GalS.Gw D.nd D.naut (D.naut.locG π w) → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w),
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        D.naut.inePol (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)) s) ∧
    (D.naut.unr (D.naut.locG π w) →
      (r '' (Ine (F := D.host.E) (D.nd.plOm.1 w) : Set (GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D))).Finite) ∧
    (D.naut.unr (D.naut.locG π w) → ∀ (B : ValuationSubring D.nd.Om) (s : GlobalTheory.IndefiniteRowSideFullHecke.RayClassPrimeCounting.GalE D),
      IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) s →
      ((r s : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        galPol D.naut (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))

structure IsAttachedAwayS : Prop where
  cont : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l))
  ss : IsSSRep r
  away : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
    UpperTheory.GalS.Aw (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r)
      (T.e w (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2)))
  temp : ∀ w : PlE D.host, ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal → D.naut.unr (D.naut.locG π w) →
    ∀ α ∈ D.naut.frobEig (D.naut.locG π w), ‖α‖ ≤ ((normV w : ℕ) : ℝ) ^ (((a : ℝ) + 3) / 2)

structure IsAttachedHodgeS : Prop extends IsAttachedAwayS D T ι π s r where
  above : ∀ w ∈ placesOver D.host.E l, ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) O), Induces Bw →
    (UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → IsDeRhamOf D ι π s r Bw) ∧
      (D.naut.unr (D.naut.locG π w) → IsCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w)) ∧
      (UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) → IsPotCrysAt (D.loc l) Bw (resDec D.nd.plOm.1 r w))

def _root_.UpperTheory.GalS.GalHodge0 : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r) (s : ℝ), D.naut.csd π → RegAlgShift D.naut π s →
    ∃ r, IsAttachedHodgeS D T ι π s r

def _root_.UpperTheory.GalS.GalHodgeN : Prop :=
  UpperTheory.GalS.GalHodge0 D T ∧ GlobalTheory.TypeLeaf.WildOne D ∧
  (∀ π : D.naut.CG D.R.r, D.naut.csd π → ∀ w w', IsConjPl D.host w w' →
    UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π w) → UpperTheory.GalS.Sep D.nd D.naut (D.naut.locG π w')) ∧
  ∀ (C₀ : Formalism.L2.Host.CharFrame D) (S : GlobalTheory.HeightCounting.CharSide D C₀) (π : D.naut.CG 1) (w : PlE D.host), (S.e1 π).1.TameAt w →
    UpperTheory.GalS.Tm D.nd D.naut (D.naut.locG π w)

variable {D T ι π s r}

theorem IsAttachedAwayS.frob (h : IsAttachedAwayS D T ι π s r) {w : PlE D.host}
    (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal) (hu : D.naut.unr (D.naut.locG π w)) :
    (∀ σ ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), r σ = 1) ∧
    ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      (r σ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
        ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) (s + (1 - (a : ℝ)) / 2))).map fun α => X - C α).prod := by
  have h1 := (D.naut.unr_tw _ (s + (1 - (a : ℝ)) / 2)).2 hu
  have e := (h.away w hl).eq_unr ((T.unr w _).1 h1)
  have h2 : (GlobalTheory.WeilDeligne.wdOf (D.nd.plOm.2 w) hl ι r).unr := by rw [e, ← T.unr]; exact h1
  refine ⟨(GlobalTheory.WeilDeligne.unr_wdOf_iff hl ι h.cont).1 h2, fun B σ hB hσ => ?_⟩
  rw [GlobalTheory.WeilDeligne.frobEig_wdOf hl ι h.cont h2 hB hσ, e, T.frobEig w _ h1]

end GlobalTheory.TripleLocal

namespace GlobalTheory.HodgeOfTrue
open GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

end G

def _root_.UpperTheory.GalS.GaloisRepsN (D : D7) : Prop :=
  ∀ π : D.naut.CG D.R.r, D.naut.csd π → D.naut.ralg π →
    ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ), ∃ r, UpperTheory.GalS.IsGaloisRepOfN D π l ι r

end GlobalTheory.HodgeOfTrue

namespace GlobalTheory.GalAway
open GlobalTheory.TripleGal _root_.Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Neutral.B1 Formalism.L2.Host GlobalTheory.HeckeGal GlobalTheory.Pst
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.HeightCounting

end GlobalTheory.GalAway
