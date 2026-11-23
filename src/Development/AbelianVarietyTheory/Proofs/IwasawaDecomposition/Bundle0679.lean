module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0677
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0047
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0008
public import Development.AutomorphicArithmetic.CharacterBoxes.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkTied
public import Formalism.SharpRestriction.GlobalSchurBounds.MainSup
public import Formalism.LocalToGlobal.GroupLattices.AdmissibleAtGeneratorPlaces
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WuDecayAll
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0005
public import Formalism.LocalToGlobal.GlobalTheory.GL5.Bundle0001
public import Formalism.LocalToGlobal.GlobalTheory.GL5.DiscreteSeriesOfFormalDegree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0008
public import Formalism.LocalToGlobal.FiniteTOf
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.STiesR
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.DivisionPairOfAdelicFormsFaceColumnsData
public import Formalism.LocalToGlobal.Bundle0002
public import Formalism.LocalToGlobal.Bundle0001
public import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.TwistedCharacterValue
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwArgs
public import Formalism.LocalToGlobal.Divisibility.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumPin
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.SingleIndexPlacesAreTwisted
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0070
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SerFixOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ExistsSmallSpherical
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidueCharacterArtinTameGaloisEqTameValue
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.OntoAlong
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RootsOfUnityRingLeWittIntegers
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsetTwistExceptionalPlaces
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ClassSumOfPin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapLevelCharacterEquivariant
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0359
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0673
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0674
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistDataAgreeAcrossCoefficientsLocalized

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BadPlacesSubOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.LevCmp.BadV

theorem unr_of_twist {R : Ranks} {H : Host R} {S : Set ℕ} {ξ : HChar H.E} (hξ : Chr.IsTwist H S ξ) {p : ℕ} (hp : p.Prime)
    (hS : p ∈ S) (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ξ.UnrAt u := by
  by_contra hn
  obtain ⟨-, h1, -, h2⟩ := hξ.2.2.2 u hn
  have h3 : ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) ∈ u.asIdeal := Ideal.absNorm_mem _
  by_cases e : Ideal.absNorm u.asIdeal = p
  · exact h2 (e ▸ hS)
  · obtain ⟨a, b, hab⟩ : IsCoprime ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 H.E) (p : 𝓞 H.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes h1 hp).2 e)
    exact u.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ Ideal.add_mem _ (Ideal.mul_mem_left _ _ h3) (Ideal.mul_mem_left _ _ hu)))

theorem not_unr_of_delta {R : Ranks} {H : Host R} {p : ℕ} {δ : HChar H.E} (hδ : IsDelta (H := H) p δ)
    (u : HeightOneSpectrum (𝓞 H.E)) (hu : OverP H p u) : ¬ δ.UnrAt u := by
  intro hn
  have h15 := (hδ.ine u hu 1).1 fun y hy => by rw [pow_one]; exact hn y hy
  exact absurd h15 (by decide)

theorem unr_of_mul_left {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ.UnrAt u) (h' : (χ * χ').UnrAt u) : χ'.UnrAt u := fun y hy => by
  have e : χ.loc u y * χ'.loc u y = 1 := h' y hy
  simpa only [h y hy, one_mul] using e

theorem unr_of_mul_right {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {u : HeightOneSpectrum (𝓞 L)}
    (h : χ'.UnrAt u) (h' : (χ * χ').UnrAt u) : χ.UnrAt u := fun y hy => by
  have e : χ.loc u y * χ'.loc u y = 1 := h' y hy
  simpa only [h y hy, mul_one] using e

end GlobalTheory.LevCmp.BadV
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BwitFrameTwists
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.RowEx GlobalTheory.Mem.LiteralAutomorphy
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowEx.FrmW

open GlobalTheory.Mem.R3 _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links GlobalTheory.Mem.Col2

variable {K : Ctx} {B : GlobalTheory.Mem.Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt} {Wt : Set B.places.Pl}
  {L : SizeData₂ (w.st Z).toD7} {hT : GatTies (w.st Z).toD7} {Gi : Formalism.MainNotions.G.Inst (w.st Z).toD7 L} {Gl : Formalism.MainNotions.G.LatInst (w.st Z).toD7}
  {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (w.st Z).toD7} {cX : ExtraC} {ex : Extra (w.st Z).toD7 L hT Gi Gl Kc Yd cX}
  {t : RowsT K w Z Wt ex.p0}


set_option maxHeartbeats 1000000 in
theorem frame_of_args (a : TwArgs ex t) (x : TwIn ex) (hx : HEq a.x x) :
    x.R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero x.R.toRealDat.toLevCh ∧
      ∀ u, ∃ ξ ∈ T.set f, HEq (x.R.toRealDat.toLevCh.xiH u) ξ := by
  obtain rfl := eq_of_heq hx
  have hz := GlobalTheory.RowEx.twisted_data_off_base_level B f T w Z _ _ t.r.z
  have e := congrArg (fun s => match s with
    | ⟨_, _, _, _, _, _, _, _, _, R, _, _⟩ => R.toRealDat.C = Fr.at (w.st Z) f ∧ TwistPlacesOffPrimeQZero R.toRealDat.toLevCh ∧
        ∀ u, ∃ ξ ∈ T.set f, HEq (R.toRealDat.toLevCh.xiH u) ξ) a.pack
  exact e.mpr ⟨hz.2.1, hz.1, fun u => ⟨_, hz.2.2.2 u, HEq.rfl⟩⟩

end GlobalTheory.RowEx.FrmW

end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesMembershipTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section

namespace GlobalTheory.TwTameCell

theorem tameAt_mul {L : Type} [Field L] [NumberField L] {χ χ' : HChar L} {v : HeightOneSpectrum (𝓞 L)}
    (h : χ.TameAt v) (h' : χ'.TameAt v) : (χ * χ').TameAt v := fun y hy hy1 => by
  change χ.loc v y * χ'.loc v y = 1
  rw [h y hy hy1, h' y hy hy1, mul_one]

theorem tameAt_one {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L)) : (1 : HChar L).TameAt v :=
  fun _ _ _ => rfl

end GlobalTheory.TwTameCell

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellPlacesOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.SepPlaces

theorem mem_of_conj {R : Ranks} (H : Host R) (p : ℕ) {w w' : HeightOneSpectrum (𝓞 H.E)}
    (h : IsConjPl H w w') : w ∈ placesOver H.E p ↔ w' ∈ placesOver H.E p := by
  have hc : ((p : 𝓞 H.E) : H.E) = H.conj ((p : 𝓞 H.E) : H.E) := by
    push_cast; exact (map_natCast _ p).symm
  exact h _ _ hc

theorem not_mem_two {E : Type} [Field E] [NumberField E] {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    {w : HeightOneSpectrum (𝓞 E)} (h1 : w ∈ placesOver E p) (h2 : w ∈ placesOver E q) : False := by
  have hc : IsCoprime (p : ℤ) (q : ℤ) := Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hpq)
  obtain ⟨a, b, hab⟩ := hc
  have h1' : ((p : ℕ) : 𝓞 E) ∈ w.asIdeal := h1
  have h2' : ((q : ℕ) : 𝓞 E) ∈ w.asIdeal := h2
  have : (1 : 𝓞 E) ∈ w.asIdeal := by
    have e : (1 : 𝓞 E) = (a : 𝓞 E) * (p : 𝓞 E) + (b : 𝓞 E) * (q : 𝓞 E) := by
      have := congrArg (Int.cast : ℤ → 𝓞 E) hab
      push_cast at this
      exact this.symm
    rw [e]
    exact w.asIdeal.add_mem (w.asIdeal.mul_mem_left _ h1') (w.asIdeal.mul_mem_left _ h2')
  exact w.isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr this)

theorem same_v (D : D7) (s s' : SplitPlace D.host.E) (h : s.v = s'.v) :
    s.w = s'.w ∨ IsConjPl D.host s'.w s.w := by
  apply GlobalTheory.SplitPlaceOver.eq_or_isConjPl D s s'.w
  show Ideal.comap _ _ = _
  rw [s'.w_under, h]

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

theorem sep_gen (D : D7) {i : D.ntw.Tw} {j : ℕ} {b : Bool} {k : ℕ} {Q : Finset (PlE D.host)}
    {ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ} {e : ℤ} {W₀ : Type} [AddCommGroup W₀]
    [Module (FractionRing (D.ntw.O i)) W₀] {ρ₀ : Representation (FractionRing (D.ntw.O i)) (GQ D.host.E D.R.nV) W₀}
    {τ : ∀ kv : (Σ kk : Fin 2, D.nd.PlG kk), (ZMod (D.host.g kv.1))ˣ →* (FractionRing (D.ntw.O i))ˣ}
    (M : NX.MtVReal D i j b k Q ψ e W₀ ρ₀ τ)
    (hQ : ∀ P ∈ Q, P ∉ D.ntw.pD i ∧ ∀ k' : Fin 2, P ∉ placesOver D.host.E (D.host.g k'))
    (P' : PlE D.host) (hP' : P' ∈ M.QP ∨ P' ∈ M.DP) :
    ¬ (P' ∈ M.QP ∧ P' ∈ M.DP) ∧ (∀ kv, (M.sp (NX.pG D kv)).v ≠ (M.sp P').v) ∧
      (∀ P'' ∈ M.QP, (M.sp P'').v = (M.sp P').v → P'' = P') ∧
      (∀ P'' ∈ M.DP, (M.sp P'').v = (M.sp P').v → P'' = P') := by
  set pX := if D.ntw.l i = D.host.pde then D.host.pde' else D.host.pde with hpX
  have hpD : ∀ P, P ∈ D.ntw.pD i ↔ P ∈ placesOver D.host.E pX := fun P => by
    rw [← Finset.mem_coe, D.ntw.pD_eq i]
  have hpXp : pX.Prime := by
    rw [hpX]; split_ifs
    · exact D.host.pde'_prime
    · exact D.host.pde_prime
  have hpXg : ∀ kk, pX ≠ D.host.g kk := fun kk => by
    rw [hpX]; split_ifs
    · exact (D.host.pde_ne_g kk).2
    · exact (D.host.pde_ne_g kk).1

  have hnotG : ∀ P, (P ∈ M.QP ∨ P ∈ M.DP) → ∀ kk, P ∉ placesOver D.host.E (D.host.g kk) := by
    rintro P (hP | hP) kk hg
    · exact (hQ P (M.QP_sub hP)).2 kk hg
    · exact not_mem_two hpXp (D.host.g_prime kk) (hpXg kk) ((hpD P).1 (M.DP_sub hP)) hg
  have hwP' : (M.sp P').w = P' := M.sp_w P' (by rcases hP' with h | h; exacts [Or.inl h, Or.inr (Or.inl h)])
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    exact (hQ P' (M.QP_sub h1)).1 (M.DP_sub h2)
  · intro kv hv
    have hwG : (M.sp (NX.pG D kv)).w = NX.pG D kv := M.sp_w _ (Or.inr (Or.inr ⟨kv, rfl⟩))
    have hG : NX.pG D kv ∈ placesOver D.host.E (D.host.g kv.1) := D.naut.plGw_over kv.1 kv.2
    rcases same_v D _ _ hv with h | h
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 (h ▸ hG)
    · rw [hwG, hwP'] at h
      exact hnotG P' hP' kv.1 ((mem_of_conj D.host _ h).2 hG)
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inl hP'')
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact M.QP_nconj P' h1 P'' hP'' h
      · exact (hQ P'' (M.QP_sub hP'')).1
          ((hpD P'').2 ((mem_of_conj D.host _ h).1 ((hpD P').1 (M.DP_sub h1))))
  · intro P'' hP'' hv
    have hw'' : (M.sp P'').w = P'' := M.sp_w P'' (Or.inr (Or.inl hP''))
    rcases same_v D _ _ hv with h | h
    · rw [hw'', hwP'] at h; exact h
    · rw [hw'', hwP'] at h
      exfalso
      rcases hP' with h1 | h1
      · exact (hQ P' (M.QP_sub h1)).1
          ((hpD P').2 ((mem_of_conj D.host _ h).2 ((hpD P'').1 (M.DP_sub hP''))))
      · exact M.DP_nconj P' h1 P'' hP'' h

end GlobalTheory.SepPlaces

namespace GlobalTheory.SepPlaces

end GlobalTheory.SepPlaces
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CellQPlacesOfAdmissibleTwist
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

namespace GlobalTheory.TameUnitOne

open Formalism.L2.NX

theorem tameVal_eq_one {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {M : Type}
    [CommGroup M] (φ : Formalism.ConjugateSelfDual.G E Ω →* M) (P : HeightOneSpectrum (𝓞 E)) (e : ℤ) (m : ℕ)
    (hopen : IsOpen (φ.ker : Set (Formalism.ConjugateSelfDual.G E Ω))) (hm : ((m : ℕ) : 𝓞 E) ∉ P.asIdeal)
    (hI : ∀ A : ValuationSubring Ω, Formalism.ConjugateSelfDual.IsPlaceOver A P → ∀ σ ∈ ReciprocityTheory.Gal.Ine (F := E) A, ∃ N : ℕ, φ σ ^ (m ^ N) = 1)
    (u : 𝓞 E) (hu1 : u - 1 ∈ P.asIdeal) : NX.tameVal φ P e u = 1 := by
  have hu : u ∉ P.asIdeal := fun h => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by
    have := P.asIdeal.sub_mem h hu1
    simpa using this))
  have hAC : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver Ω P
  obtain ⟨hq2, -⟩ := GlobalTheory.TameValChar.two_le_normV_and_not_mem P
  obtain ⟨ϖ, hϖ1, hϖ2⟩ : ∃ ϖ : 𝓞 E, ϖ ∈ P.asIdeal ∧ ϖ ∉ P.asIdeal ^ 2 := by
    have hlt := Ideal.pow_succ_lt_pow (P := P.asIdeal) P.ne_bot 1
    rw [pow_one] at hlt
    obtain ⟨x, hx, hx'⟩ := SetLike.exists_of_lt hlt
    exact ⟨x, hx, hx'⟩
  have hϖne : algebraMap E Ω (ϖ : E) ≠ 0 := by
    intro h
    apply hϖ2
    have h' : ((ϖ : E)) = 0 := (map_eq_zero _).1 h
    rw [show ϖ = 0 from RingOfIntegers.coe_eq_zero_iff.1 h']
    exact zero_mem _
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (algebraMap E Ω (ϖ : E)) (show 0 < Formalism.ConjugateSelfDual.normV P - 1 by omega)
  have hπne : π ≠ 0 := by
    rintro rfl
    rw [zero_pow (by omega)] at hπ
    exact hϖne hπ.symm
  have hv : A.valuation ((1 : Formalism.ConjugateSelfDual.G E Ω) π / π - algebraMap E Ω (u : E)) < 1 := by
    rw [AlgEquiv.one_apply, div_self hπne]
    have h1 := (hA (u - 1)).2 hu1
    have e1 : (1 : Ω) - algebraMap E Ω (u : E) = -(algebraMap E Ω (((u - 1 : 𝓞 E)) : E)) := by
      push_cast
      ring
    rw [e1, Valuation.map_neg]
    exact h1
  have hT := GlobalTheory.TameResRead.tameRep_zpow hA (one_mem _) hϖ1 hϖ2 hπ hu hv e
  rw [GlobalTheory.TameResRead.tameVal_eq_of_tameRep φ P e m hopen hm hI _ u hu hT, one_zpow, map_one]

end GlobalTheory.TameUnitOne

namespace GlobalTheory.LevCmp

end GlobalTheory.LevCmp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassSumDivisibilityBundle
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.RT GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BigTop

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem classSumPin_of_read (p : PtAt ex Csz) (Yr : R3.Read (A3 := p.P.A3) p.R.toRealDat p.F.lv2 ex.p0)
    (hjW : ∀ (i : Fin D.R.m) (v : Fin ((p.P.A3.indefDown p.P.S0).dW i) → D.what₂.LL)
      (y : Fin (Module.finrank D.what₂.LL (p.R.toRealDat.WL p.F.lv2 false i)) → D.what₂.LL), HEq v y →
      Yr.mj.eW i (p.P.I.jW i v) = (p.R.FW i).j (sg0 D p.P.A3.A) (jDL p.R p.F.lv2 i y))
    (hth : GlobalTheory.HeightCounting.EMtTheta Yr p.nexp ex.nch)
    (hD : DivRows3 D p.P.A3 p.P.P0 p.P.ψ0 p.P.Ps p.P.ψs p.P.Zs p.P.S0 p.P.S1 ex.p0 p.P.C p.P.NuC p.P.I) :
    GlobalTheory.ExportPin.ClassSumPin p := by
  intro w i h1 h2 t ht hw c x hx hxT y hy n a f hsum
  subst hx
  apply hth w i hw _ hxT n a f
  rw [hsum, GlobalTheory.ExportPin.Model.theta_cast _ _ _ ht, hD.thTheta, hjW i _ y hy]

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX

section Pack

variable {D : D7} {O : Obj D}




end Pack

end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink

open _root_.Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX


set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem eMtTheta_of_pack {D : D7} {nch : NChoice D} {X0 : BaseLevelRowSide D} {G G' : Type} {g : Group G} {g' : Group G'} {fi : Fintype G}
    {fi' : Fintype G'} {Pl0 I0 T Pl0' I0' T' : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}
    {A3' : FamIn3 D.what₂.LL G' Pl0' I0' (List ℕ) T' D.R.m}
    {C C' : CoreJ D} {al : Algebra C.Q.c.F D.what₂.LL} {al' : Algebra C'.Q.c.F D.what₂.LL} {R : RealDat3 D A3 C.Q.c.F}
    {R' : RealDat3 D A3' C'.Q.c.F} {F : Face3 D A3} {F' : Face3 D A3'} {kap : ℝ} {lam : type_of% R'.lam3} {err : type_of% R'.err0}
    {Dc : ∀ Zs : DefSub A3'.fam3.amb3, DefCols (A3'.side3 F'.P1 F'.ψ1 Zs)} {Sp : ∀ Zs, SPer (Dc Zs)}
    {Zsc : DefSub A3'.fam3.amb3 → IndefScale A3'.fam3.base3}
    {cG : G0 R.Pg D.R.r ≃* G0g D.nd} {cG' : G0 R'.Pg D.R.r ≃* G0g D.nd}
    {cG'' : G0 ((R'.updS kap lam).withErr err).Pg D.R.r ≃* G0g D.nd}
    (pack : (⟨G, g, fi, Pl0, I0, T, A3, C, al, R, F, cG⟩ :
      Σ' (G : Type) (_ : Group G) (_ : Fintype G) (Pl0 I0 T0 : Type)
        (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T0 D.R.m) (C : CoreJ D)
        (_ : Algebra C.Q.c.F D.what₂.LL) (R : RealDat3 D A3 C.Q.c.F) (_ : Face3 D A3),
        G0 R.Pg D.R.r ≃* G0g D.nd) =
      ⟨G', g', fi', Pl0', I0', T', A3', C', al', (R'.updS kap lam).withErr err, R3.reFace F' Dc Sp Zsc, cG''⟩)
    (Y : R3.Read (A3 := A3) R.toRealDat F.lv2 X0) (Y' : R3.Read (A3 := A3') R'.toRealDat F'.lv2 X0)
    (hW : HEq Y.mj.eW Y'.mj.eW) {S S' : RatDat D.ntw} (hS : S = S')
    (E : NExpRealS R cG S) (E' : NExpRealS R' cG' S') (hF : HEq E.eF E'.eF) (hi : HEq E.fi E'.fi)
    (h : GlobalTheory.HeightCounting.EMtTheta Y' E' nch) : GlobalTheory.HeightCounting.EMtTheta Y E nch := by
  cases pack
  cases hS
  intro w i hw x hx n a f hs
  have e1 : E.eF = E'.eF := eq_of_heq hF
  have e2 : E.fi = E'.fi := eq_of_heq hi
  have e3 : Y.mj.eW = Y'.mj.eW := eq_of_heq hW
  rw [e2, e3] at hs
  rw [e1]
  exact h w i hw x hx n a f hs


end GlobalTheory.ClassSumPinLink

namespace GlobalTheory.ClassSumPinLink


end GlobalTheory.ClassSumPinLink
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapLevelCharacterEquivariantStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 GlobalTheory.Mem.Col2
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coefficient_map_level_character_equivariant : ∀ (X : Stages) (px : PreX X.B.toPre) (I : Col2.ColIn X.B px) (hX : X.B.fields.Ok) (U : Set I.ι) (Xg : Finset (Gc X.B px → X.B.LL)) (tr : TrI X.B px) (L : Formalism.IndefR.Links.LevCh X.toD7 (TupU I U)) (eG : Gc X.B px ≃* G0 L.Pg X.toD7.R.r), I.Ok → ValsIn I → LevOf X I U L → IsPlacewiseIdentity X (px := px) eG → L.βX = 1 → ∀ (cX : CoefA X.toD7.sp.X') (c : VV X.B.fields.K X.B.wts.sgTrue →ₛₗ[X.B.embLL] cX.W), (∀ (γ : GQ X.toD7.sp.X') (γE : GL (Fin X.toD7.sp.X'.rank) X.toD7.host.E) (g : GL (Fin (X.B.R.N X.B.R.m - 1)) X.B.fields.E), Bridge.IsRatMat X.toD7.sp.X' γ γE → MatEq γE g → ∀ v, c (rhoV X.B.fields.emb X.B.wts.sgTrue g v) = cX.coef.ρ γ (c v)) → LinearIndependent ℂ (fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) → Submodule.span ℂ (Set.range fun i => c (bVV X.B.fields.K X.B.wts.sgTrue i)) = ⊤ → (∀ x y, inner ℂ (c x) (c y) = X.B.embLL (pairV X.B.fields.emb X.B.wts.sgTrue 1 x y)) → ∀ t, ∃ P : Bridge.ClassPres (Bridge.ratF X.toD7.sp.X') ((famR X I hX U Xg tr).A.MtildeCSD t) X.toD7.what₂.embLL cX.coef.ρ (levEnv X.toD7.sp.X' L.βX (L.datXt t)).J (levEnv X.toD7.sp.X' L.βX (L.datXt t)).χ, (∀ x, P.coef x = c x) ∧ (∀ c', RowAd.decoAd X I t (P.y c') = (Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).outSec.rep c') ∧ ∀ (f : ((famR X I hX U Xg tr).A.MtildeCSD t).Forms) (h : Bridge.Gf X.toD7.sp.X'), P.ext (f : _ → _) h = c ((((Formalism.L2.Col.mtildeKGSD (Pr := X.B.primes px) X.B.wts I.Ch I.sel t.1).res (Formalism.L2.Col.mtildeKOk _ _ _ _ hX)).symm f).1 (RowAd.decoAd X I t h)) := by
  first | exact @GlobalTheory.Mem.R3.RowStdPres.exists_pres | exact GlobalTheory.Mem.R3.RowStdPres.exists_pres | (intros; apply GlobalTheory.Mem.R3.RowStdPres.exists_pres <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompositeIntertwinerEqThetaLiftGoodProjectorStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → (∀ t x, (Y.Ish.jE (D.what₂.iota (Y.tup t) (Y.jA t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P1 F.ψ1 t x))))) ∧ ∀ t x, (Y.Iz.jE (X0.s.iota (Y.tup t) (Y.jA0 t x))).1 = PiTensorProduct.lift (R.HE.e (R.Th t (R.jX t (rowForm A3.A F.P0 F.ψ0 t x)))) := by
  first | exact @GlobalTheory.Mem.R3.DTheta.composite_eq_lift | exact GlobalTheory.Mem.R3.DTheta.composite_eq_lift | (intros; apply GlobalTheory.Mem.R3.DTheta.composite_eq_lift <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovedDataStateLocalisationsStatement
section
namespace GlobalTheory.T

alias exists_movedData_state_localisations := GlobalTheory.HeightCounting.Fin3.MvLoc.exists_moved_loc

end GlobalTheory.T
end

