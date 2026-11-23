module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0002
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0003
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0007
public import Formalism.LocalRingCardinality.DataIdx
public import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TwistBaseCoefficientRingResidueFieldFinite
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0007
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KerMtPin
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceModelImp

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.L2.Host GlobalTheory.CuspRep NumberField IsDedekindDomain

structure CGTrue (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) where
  e : ∀ a, D.naut.CG a ↪ HostCGu D.host a
  surj : ∀ a, 0 < a → Function.Surjective (e a)
  zero : IsEmpty (D.naut.CG 0)
  loc : ∀ a (π : D.naut.CG a) w, T.e w (D.naut.locG π w) = ParLaws.locG hL D.nd.plOm (e a π) w
  tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ)
  inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ
  csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd

def wdCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) :
    GlobalTheory.RowTie.WDTie (setCG D hE K).nd (setCG D hE K).naut := { T with }

def cfCG {D : D7} (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) (c : CharFrame D) : CharFrame (setCG D hE K) :=
  ⟨c.P, c.W, c.mu0, c.eta, c.chiPsi, c.del, c.del', c.isMu0, c.isEta, c.isChi, c.isDel, c.isDel'⟩

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteTwistFrameExtraExcludedOverSmallPrimes
section
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.FrobeniusOrbits Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC Formalism.L2.NC NumberField IsDedekindDomain
  Polynomial
open scoped TensorProduct NNReal

section
variable (D : D7)

def KQbar (jE : D.host.E →+* Qb) : Fld := D.host.K.map jE.toRatAlgHom

def MrayC (jE : D.host.E →+* Qb) : Fld := rayField (KQbar D jE) (D.host.QS * D.host.q * D.host.d)

def ParC : Type :=
  {Sig : List (Part D.naut.CG) //
    (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π) ∧
    (Sig.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup ∧
    rankIso D.nd D.naut Sig = D.R.r ∧
    ∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).Monic ∧
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree = D.R.r}

structure GrpSide where
  tA : Fin 2 → ValuationSubring ℂ
  tκ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (tA k) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)
  teichC_def : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsTeich (tA k) (tκ k) (D.ntypes.teichC k)
  ζ : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    ℕ → Formalism.CyclotomicNorms.Fbar (D.host.g k)
  ζ_gen : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsGenSys (ζ k)
  O : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod (D.host.g k)) (convC (D.ntypes.teichC k) (D.ntypes.teichC_inj k) (ζ k) (ζ_gen k))
  eSer_def : ∀ k f, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    D.ntypes.eSer k f = eSerO (O k) D.R.r f
  kv : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    IsLocalRing.ResidueField (D.nd.plOm.1 (D.naut.plGw k v)) ≃+* Formalism.CyclotomicNorms.Fbar (D.host.g k)
  tg_tame : ∀ k (v : D.nd.PlG k), haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    TameCoupled (D.nd.plOm.1 (D.naut.plGw k v)) (kv k v) (D.ntypes.tg k v) (ζ k)
  O_equiv : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    Formalism.IrreducibleCountingLemmas.TYPES.LabelMapEquivariant (O k)
  O_tw : ∀ k, haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
    LabTwLawO (O k)

structure ParSide (jE : D.host.E →+* Qb) where
  eM : D.ntypes.Mray ≃+* MrayC D jE
  eM_K : ∀ x : D.host.K, ((eM (algebraMap D.host.K D.ntypes.Mray x) : MrayC D jE) : Qb) = jE x
  eP : D.ntypes.Par ≃ ParC D
  locPar_def : ∀ σ w, D.ntypes.locPar σ w = isoLoc D.nd D.naut (eP σ).1 w

def IotaOk (Pl : PlSide D) : Prop :=
  ∀ lam k v x, D.ntypes.iota k v lam x = redThrough (Pl.plB lam) (Pl.plκ lam) (D.ntypes.teichC k x)

end

abbrev Big (D : D7) : Type := ∀ (l : ℕ) [Fact l.Prime], (↥D.LL0 →+* PadicAlgCl l) → Loc.FinExt l


set_option synthInstance.maxHeartbeats 400000 in
structure RingSpec (D : D7) (cf : CharFrame D) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) where
  eTw : T.Tw ≃ HeightOneSpectrum (𝓞 ↥D.LL0)
  pl_emb : ∀ i, ((T.l i : ℕ) : 𝓞 ↥D.LL0) ∈ (eTw i).asIdeal ∧
    ∀ x : 𝓞 ↥D.LL0, x ∈ (eTw i).asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (T.O0 i),
      algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = T.emb0 i (x : ↥D.LL0)
  K0 : ∀ i, Loc.FinExt (T.l i)
  eO0 : ∀ i, T.O0 i ≃+* intOf (T.l i) (K0 i).1
  j0 : ∀ i, ↥D.LL0 →+* PadicAlgCl (T.l i)
  Lw : ∀ i, Loc.FinExt (T.l i)
  eO : ∀ i, T.O i ≃+* clC (T.l i) (Kt (T.l i) (K0 i) (Lw i))
  eOk : ∀ i k, T.Ok i k ≃+* clC (T.l i) (Kt (T.l i) (K0 i) (Lw i) ⊔ muK (T.l i) k)
  iCq : ∀ i, FractionRing (T.O i) →+* ℂ
  ringSpec_baseExtension_lowerBound : ∀ i, (b0 (T.l i) (j0 i)).1 ≤ (K0 i).1
  Lw_big : ∀ i, (b1 (T.l i) (j0 i)).1 ≤ (Lw i).1
  ringSpec_baseIntegersEquiv_algebraMap : ∀ i (z : ℤ_[T.l i]),
    ((eO0 i (algebraMap ℤ_[T.l i] (T.O0 i) z) : PadicAlgCl (T.l i))) =
      algebraMap ℚ_[T.l i] (PadicAlgCl (T.l i)) (z : ℚ_[T.l i])
  ringSpec_baseEmbedding_compatible : ∀ i (x : ↥D.LL0) (y z : T.O0 i), z ≠ 0 →
    (T.emb0 i x * algebraMap (T.O0 i) (FractionRing (T.O0 i)) z =
        algebraMap (T.O0 i) (FractionRing (T.O0 i)) y ↔
      j0 i x * (eO0 i z : PadicAlgCl (T.l i)) = (eO0 i y : PadicAlgCl (T.l i)))
  eO_alg : ∀ i (y : T.O0 i), ((eO i (algebraMap (T.O0 i) (T.O i) y) : ℂ_[T.l i])) =
    algebraMap (PadicAlgCl (T.l i)) ℂ_[T.l i] (eO0 i y : PadicAlgCl (T.l i))
  eOk_alg : ∀ i k (x : T.O i), ((eOk i k (algebraMap (T.O i) (T.Ok i k) x) : ℂ_[T.l i])) =
    (eO i x : ℂ_[T.l i])
  mu_g : ∀ i k, T.l i = D.host.g k → muK (T.l i) 1 ≤ Kt (T.l i) (K0 i) (Lw i)
  ringSpec_excludedPlaces_eq : ∀ i, (T.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E))) =
    placesOver D.host.E (T.l i) ∪ (⋃ k, placesOver D.host.E (D.host.g k)) ∪
      placesOver D.host.E D.host.pde ∪ placesOver D.host.E D.host.pde' ∪ ↑Sx
  br : ∀ (i : T.Tw) (w : PlE D.host), w ∈ placesOver D.host.E (T.l i) →
    LocBridge (T.l i) D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) (T.O0 i)
  br_ind : ∀ i w (hw : w ∈ placesOver D.host.E (T.l i)) (x : D.nd.Om), x ∈ D.nd.plOm.1 w ↔ ‖(br i w hw).j x‖ ≤ 1
  mu0H : ℕ → HC D.host.E
  etaH : HC D.host.E
  delH : T.Tw → HC D.host.E
  embO : ∀ s, Bool → ↥D.LL0 →+* FractionRing (T.O s)
  del_fix : ∀ s s', T.pD s = T.pD s' → delH s = delH s'
  delta : ∀ s, Read D.nd.plOm.1 (T.delta s) (algebraMap (T.O0 s) (FractionRing (T.O0 s))) (T.emb0 s)
    (embLL0 D) (delH s) 0
  chi1 : ∀ s j (b : Bool), 1 ≤ j → j ≤ D.R.m → Read D.nd.plOm.1 (T.chi1 s j b) (algebraMap (T.O0 s) (FractionRing (T.O0 s)))
    (if b then T.emb0 s else T.emb0b s) (embLL0 D) (mu0H j * delH s * etaH⁻¹) (-(D.R.r : ℤ))
  ringSpec_sidedEmbedding_fixedField : ∀ s (b : Bool) (x : ↥D.LL0) (y : T.O0 s),
    algebraMap (T.O0 s) (FractionRing (T.O0 s)) y = (if b then T.emb0 s else T.emb0b s) x →
    embO s b x = algebraMap (T.O s) (FractionRing (T.O s)) (algebraMap (T.O0 s) (T.O s) y)
  etaT_unr : ∀ P, etaH.Unr P
  etaT_inf : ∀ g : D.R.Psi, etaH.IsUnitArg (D.host.emb (g : D.R.GG))
  eta_eq : ∀ x, etaH.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (mu0H (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (delH s).χ x = (cf.delAt (T.l s)).1 x
  iCq_embO : ∀ s (x : ↥D.LL0), iCq s (embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → embO s false x = embO s true y
  deltaRead : ∀ (s : T.Tw) (w : PlE D.host), w ∉ placesOver D.host.E (T.l s) → (cf.delAt (T.l s)).UnrAt w →
    ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om), IsPlaceOver (F := D.host.E) B w →
      IsFrob (F := D.host.E) B (normV w) σ →
      ∃ x : D.LL0, D.what₂.embLL (x : D.what₂.LL) = (((cf.delAt (T.l s)).val w)⁻¹ : ℂˣ).1 ∧
        algebraMap (T.O0 s) (FractionRing (T.O0 s)) ((T.delta s σ : (T.O0 s)ˣ) : T.O0 s) = T.emb0 s x


set_option synthInstance.maxHeartbeats 400000 in
structure TwFrameC (D : D7) where
  K0 : ∀ i, Loc.FinExt (D.ntw.l i)
  eO0 : ∀ i, D.ntw.O0 i ≃+* intOf (D.ntw.l i) (K0 i).1
  j0 : ∀ i, ↥D.LL0 →+* PadicAlgCl (D.ntw.l i)
  Lw : ∀ i, Loc.FinExt (D.ntw.l i)
  eO : ∀ i, D.ntw.O i ≃+* clC (D.ntw.l i) (Kt (D.ntw.l i) (K0 i) (Lw i))
  eOk : ∀ i k, D.ntw.Ok i k ≃+* clC (D.ntw.l i) (Kt (D.ntw.l i) (K0 i) (Lw i) ⊔ muK (D.ntw.l i) k)
  iCq : ∀ i, FractionRing (D.ntw.O i) →+* ℂ
  S0x : D.ntw.Tw → Finset (HeightOneSpectrum (𝓞 D.host.E))


set_option synthInstance.maxHeartbeats 400000 in
structure TwistFrameLowIndexCompatibility (D : D7) (F : TwFrameC D) (low : Finset ℕ) : Prop where
  pl_emb : ∀ i, ∃ w : HeightOneSpectrum (𝓞 ↥D.LL0), ((D.ntw.l i : ℕ) : 𝓞 ↥D.LL0) ∈ w.asIdeal ∧
    ∀ x : 𝓞 ↥D.LL0, x ∈ w.asIdeal ↔ ∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : ↥D.LL0)
  ringSpec_baseIntegersEquiv_algebraMap : ∀ i (z : ℤ_[D.ntw.l i]),
    ((F.eO0 i (algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) z) : PadicAlgCl (D.ntw.l i))) =
      algebraMap ℚ_[D.ntw.l i] (PadicAlgCl (D.ntw.l i)) (z : ℚ_[D.ntw.l i])
  ringSpec_baseEmbedding_compatible : ∀ i (x : ↥D.LL0) (y z : D.ntw.O0 i), z ≠ 0 →
    (D.ntw.emb0 i x * algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) z =
        algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y ↔
      F.j0 i x * (F.eO0 i z : PadicAlgCl (D.ntw.l i)) = (F.eO0 i y : PadicAlgCl (D.ntw.l i)))
  eO_alg : ∀ i (y : D.ntw.O0 i), ((F.eO i (algebraMap (D.ntw.O0 i) (D.ntw.O i) y) : ℂ_[D.ntw.l i])) =
    algebraMap (PadicAlgCl (D.ntw.l i)) ℂ_[D.ntw.l i] (F.eO0 i y : PadicAlgCl (D.ntw.l i))
  eOk_alg : ∀ i k (x : D.ntw.O i), ((F.eOk i k (algebraMap (D.ntw.O i) (D.ntw.Ok i k) x) : ℂ_[D.ntw.l i])) =
    (F.eO i x : ℂ_[D.ntw.l i])
  mu_g : ∀ i k, D.ntw.l i = D.host.g k → muK (D.ntw.l i) 1 ≤ Kt (D.ntw.l i) (F.K0 i) (F.Lw i)
  hk_split : ∀ i j b k P, P ∉ D.ntw.S0 i → ∃ s : Multiset (FractionRing (D.ntw.O i)),
    (LinearMap.charpoly (D.ntw.hk i j b k P)).map (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i))) =
      (s.map fun a => X - C a).prod
  ringSpec_excludedPlaces_eq : ∀ i, (D.ntw.S0 i : Set (HeightOneSpectrum (𝓞 D.host.E))) =
    placesOver D.host.E (D.ntw.l i) ∪ (⋃ k, placesOver D.host.E (D.host.g k)) ∪
      placesOver D.host.E D.host.pde ∪ placesOver D.host.E D.host.pde' ∪ ↑(F.S0x i)
  concreteTwistFrame_extraExcludedPlaces_conj : ∀ i P P', P ∈ F.S0x i → IsConjPl D.host P P' → P' ∈ F.S0x i
  B_range : ∀ i j b, LinearMap.range (D.nexp.embB i j b) =
    D.nexp.Bsup i j b ⊓ (NForms.V0 D i j b).restrictScalars (D.ntw.O i)
  sig_inj : ∀ i (s s' : D.ntw.Sig i), D.ntw.jS i s = D.ntw.jS i s' → D.ntw.side i s = D.ntw.side i s' →
    (∀ k P, 1 ≤ k → k ≤ D.R.r → IsSplitPl D.host P → P ∉ D.ntw.S0 i →
      D.ntw.hEig i s k P = D.ntw.hEig i s' k P) → s = s'
  qs_pos : ∀ i lam P, P ∉ D.ntw.S0 i →
    F.iCq i (D.ntw.qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(D.ntw.s2 i lam : ℝ) / 2) : ℝ) : ℂ)
  concreteTwistFrame_extraExcluded_over_smallPrimes : ∀ i, ∀ p ∈ low, placesOver D.host.E p ⊆ ↑(F.S0x i)

def RhoSpec (D : D7) (Rw : RowSide D) (rowS : ∀ i, D.ntw.Sig i → D.what₂.FT) : Prop :=
  ∀ i (s : D.ntw.Sig i), D.what₂.isot (D.ntw.jS i s) (rowS i s) ≠ ⊥ ∧ D.nd.goodRow (rowS i s) ∧ ∀ π : D.naut.CG D.R.r,
    D.naut.csd π → D.naut.ralg π → (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR (rowS i s) w) →
    ∀ (φ : FractionRing (D.ntw.O0 i) →+* Qbar (D.ntw.l i)) (ι : Qbar (D.ntw.l i) ≃+* ℂ),
      (∀ z : ℤ_[D.ntw.l i], φ (algebraMap (D.ntw.O0 i) _ (algebraMap ℤ_[D.ntw.l i] (D.ntw.O0 i) z)) =
        algebraMap ℚ_[D.ntw.l i] (Qbar (D.ntw.l i)) (z : ℚ_[D.ntw.l i])) →
      (∀ x : ↥D.LL0, ι (φ ((if D.ntw.side i s then D.ntw.emb0 i else D.ntw.emb0b i) x)) = embLL0 D x) →
      IsRepOf D (D.ntw.l i) ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2)
        (mapRep (φ.comp (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)))) (D.ntw.rhoS i s))

def SidePl (D : D7) (w : D.what₂.places.Pl) (i : D.ntw.Tw) (s : Bool) : Prop :=
  ∀ x : D.LL0, 0 ≤ D.what₂.places.val w (x : D.what₂.LL) ↔
    (if s then D.ntw.emb0 i x else D.ntw.emb0b i x) ∈ (algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).range

def twPackPow (D : D7) (a : ℤ) (p : TwPack D) : TwPack D :=
  ⟨p.1, p.2.1, p.2.2.1, p.2.2.2 ^ a⟩

def fracOe (D : D7) (C : NChoice D) (w : D.what₂.places.Pl) : FractionRing (D.ntw.O0 (C.twI w)) →+* FractionRing (C.Oe w) :=
  IsFractionRing.map (j := (algebraMap (D.ntw.Ok (C.twI w) (C.k' w)) (C.Oe w)).comp
      ((algebraMap (D.ntw.O (C.twI w)) (D.ntw.Ok (C.twI w) (C.k' w))).comp (algebraMap (D.ntw.O0 (C.twI w)) (D.ntw.O (C.twI w)))))
    ((C.Oe_inj w).comp ((D.ntw.Ok_inj (C.twI w) (C.k' w)).comp (D.ntw.O_inj (C.twI w))))

structure ChoiceC (D : D7) (C : NChoice D) : Prop where
  twI_conj : ∀ w, C.twI (D.what₂.places.conj w) = C.twI w
  sd_place : ∀ w, TwistedAt D w → SidePl D w (C.twI w) (C.sd w)
  emb_side : ∀ w, TwistedAt D w → ∀ (x : D.LL0), C.embW w (x : D.what₂.LL) =
    fracOe D C w (if C.sd w then D.ntw.emb0 (C.twI w) x else D.ntw.emb0b (C.twI w) x)
  sd_conj : ∀ w, TwistedAt D w → D.what₂.places.conj w ≠ w → C.sd (D.what₂.places.conj w) = !C.sd w
  one : ∀ w w', TwistedAt D w → TwistedAt D w' → C.twI w' = C.twI w →
    ∃ a : ℤ, Nat.Coprime a.natAbs (D.ntw.l (C.twI w)) ∧ NChoicePack C w' = twPackPow D a (NChoicePack C w)
  conj : ∀ w, TwistedAt D w → NChoicePack C (D.what₂.places.conj w) = NChoicePack C w

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsSameFOfDiv
section
noncomputable section

namespace GlobalTheory.Mem.SRe

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict Formalism.L2.SG.RowDict Formalism.L2.Forms Formalism.L2.SG.TermOp Formalism.L2.SG.Full

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (Z : New D)

set_option maxHeartbeats 4000000

def SPack.re {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F')
    (hF : FinX (reY Z P.Y)) : SPack (reD D Z) F' where
  X := reX Z P.X
  hb := (by with_unfolding_all exact (P.hb :))
  Y := reY Z P.Y
  fin := hF
  ψ := (by with_unfolding_all exact (P.ψ :))
  measTie := (by with_unfolding_all exact (measTie_reX Z P.measTie :))
  ψ_char := (by with_unfolding_all exact (P.ψ_char :))
  ψ_std := (by with_unfolding_all exact (P.ψ_std :))
  measCompat := (by with_unfolding_all exact (measCompat_reX Z P.measCompat :))
  locCompat := (by with_unfolding_all exact (fun w : D.what₂.Word => locCompat_reX Z (P.locCompat w) :))
  tr := (by with_unfolding_all exact (fun u : D.what₂.Word => reTr Z (P.tr u) (h u).2.1 (h u).2.2 :))
  into := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictInto_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.into u) :))
  bij := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictBij_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y (P.bij u) :))
  lev := (by with_unfolding_all exact (fun u : D.what₂.Word => levelMatch_reTr Z (P.tr u) (h u).1 (h u).2.1 (h u).2.2 P.Y (P.lev u) :))
  isom := (by with_unfolding_all exact (fun u : D.what₂.Word => colDictIsom_reTr Z (P.tr u) (h u).2.1 (h u).2.2 P.Y P.fin hF (P.isom u) :))
  inst := (by with_unfolding_all exact (P.inst :))
  G := reG Z P.G
  pin := (by with_unfolding_all exact (P.pin :))

section API

variable {F : ∀ u, Forms0 D u} (P : SPack D F) {F' : ∀ u, Forms0 (reD D Z) u} (h : SameForms0LevelsAndValues Z F F') (hF : FinX (reY Z P.Y))

end API

theorem conjHH_eEECre {X : HidaSetting D} (G : GoodOp X) (x : EEC X G) :
    conjHH (reX Z X) (reG Z G) (eEECre Z G x) = eHHre Z X (conjHH X G x) := (by with_unfolding_all exact (Eq.refl (eHHre Z X (conjHH X G x)) :))

theorem exists_sameF_ofDiv (N : ∀ u, Submodule (𝓞 D.what₂.LL) (D.div.Nu u).V) (ht : D.what₂.Word → ℝ) (F : ∀ u, Forms0 D u) :
    ∃ F' : ∀ u, Forms0 (reD D (New.ofDiv D N ht)) u, SameForms0LevelsAndValues (New.ofDiv D N ht) F F' := by
  let G : ∀ u : D.what₂.Word, Forms0 (GlobalTheory.EX.OB.setDiv D N ht) u := fun u =>
    { F u with
      atT := { (F u).atT with }
      cls0 := { (F u).cls0 with }
      val0 := { (F u).val0 with }
      lv0 := { (F u).lv0 with } }
  refine ⟨(by with_unfolding_all exact (G :)), fun u => ⟨?_, ?_, ?_⟩⟩
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.lev :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).cls0.y :))
  · exact (by with_unfolding_all exact (Eq.refl (F u).val0.eY :))

end GlobalTheory.Mem.SRe

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
section
noncomputable section

namespace GlobalTheory.Mem.Col2.TC

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Chr Formalism.UG Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : Later B (I.cols l))

def TopPt (u : B.Word) (a : I.ι) (k : GA B (B.R.N B.R.m)) : Prop :=
  ∀ (d : XPt (B.primes X) B.R I.sel (I.tup a)) (g' : GA B (B.R.N B.R.m - 1)) (g : GA B (B.R.N B.R.m)), PtOf g' d →
    IsExt (I.rec7 l Z) (z0 X u) (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) g'.1 g.1 →
    PtOf (g * k) (tilF I.sel (I.tup a) u d)


section Tw

variable (l0 : I.Law0 l) {inQ : (I.rec7 l Z).what₂.Tup → HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) → Prop}
  {T : Formalism.L2.Herm.TwChTied (I.rec7 l Z) inQ} {H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)} {J : Formalism.L2.Herm.TwChJointS T H}
  {F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)}

structure StdP {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W} (P : TwPTiedS Lv) (E : TwPEvzS P) : Prop where

  what₂ : ∀ u a ha, I.ReadsP a (P.cls u a ha).lev.Lb (P.cls u a ha).lev.U (P.cls u a ha).lev.chi (fun c => ((P.cls u a ha).y c).1)
    (P.cls u a ha).lat fun c s => ((P.cls u a ha).stabI c s).1

  eW : ∀ u a ha z c (s : FrP (I.rec7 l Z)) s', s'.1 = s.1 → (P.val u a ha).eW z c s = z c s'

  z0 : ∀ u a ha h1, (P.til u a ha h1).z0 = TC.z0 X u

  eWz : ∀ u a z, E.eWz u a z = z

variable {I l Z l0} {W : TwFormsTiedS (I.rec7 l Z) (I.tw l l0 Z) T J F} {Lv : SymmetricTwistedLevelData W}

end Tw

def StdTw (l0 : I.Law0 l) {cf : Formalism.L2.Host.CharFrame (I.rec7 l Z)} {nch : NChoice (I.rec7 l Z)}
    {tp : Formalism.L2.Host.TupTied (I.rec7 l Z) cf nch} {C : ColsTiedSym (I.rec7 l Z)} (t : SymmetricTwistedColumnsAtPrimes tp C (I.tw l l0 Z)) : Prop :=
  I.StdW l Z l0 t.forms ∧ I.StdLv l Z l0 t.lv ∧ I.StdP l Z l0 t.pt t.ptE

def EntOk {D : D7} {Y : DivX D} {Tw : TwForms D} (E : KerEnt D Y Tw) (O : ∀ u μ, GL3Theta.LiftObj D (D.chTw u μ)) : Prop :=
  (∃ kf : ∀ u μ w, LevFree Y u μ w → GL3Columns.KFTie E (O u μ) w, ∀ u μ w (h : LevFree Y u μ w), (kf u μ w h).UnIs) ∧ AdaptedTh E O

end GlobalTheory.Mem.Col2.TC

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealIoX
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

def real {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @RealDat b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) :=
  @RealDat.mk b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK)
    (toLevCh := levCh b R.toLevCh)
    (hv0 := (by with_unfolding_all exact (R.hv0 :)))
    (eG := (by with_unfolding_all exact (R.eG :)))
    (pl := (by with_unfolding_all exact (R.pl :)))
    (Sb := (by with_unfolding_all exact (R.Sb :)))
    (θ := (by with_unfolding_all exact (R.θ :)))
    (ψ := (by with_unfolding_all exact (R.ψ :)))
    (MY := fun j => (by with_unfolding_all exact ((ds b (R.MY j)) :)))
    (MX := (by with_unfolding_all exact ((ds b R.MX) :)))
    (MW := fun i σ => (by with_unfolding_all exact ((ds b (R.MW ((by with_unfolding_all exact (i :))) ((by with_unfolding_all exact (σ :))))) :)))
    (cX := (by with_unfolding_all exact ((coefA b R.cX) :)))
    (cV := fun i => (by with_unfolding_all exact ((coefA b (R.cV ((by with_unfolding_all exact (i :))))) :)))
    (B := (by with_unfolding_all exact ((famReal b R.B) :)))
    (prX := (by with_unfolding_all exact (R.prX :)))
    (HX := (by with_unfolding_all exact (R.HX :)))
    (HV := (by with_unfolding_all exact (R.HV :)))
    (HE := (by with_unfolding_all exact (R.HE :)))
    (HW := (by with_unfolding_all exact (R.HW :)))
    (gE := (by with_unfolding_all exact (R.gE :)))
    (gW := (by with_unfolding_all exact (R.gW :)))
    (jX := (by with_unfolding_all exact (R.jX :)))
    (jV := (by with_unfolding_all exact (R.jV :)))
    (νY := (by with_unfolding_all exact (R.νY :)))
    (fdY := (by with_unfolding_all exact (R.fdY :)))
    (ν0 := (by with_unfolding_all exact (R.ν0 :)))
    (fd0 := (by with_unfolding_all exact (R.fd0 :)))
    (νX := (by with_unfolding_all exact (R.νX :)))
    (fdX := (by with_unfolding_all exact (R.fdX :)))
    (νV := (by with_unfolding_all exact (R.νV :)))
    (fdV := (by with_unfolding_all exact (R.fdV :)))
    (νW := (by with_unfolding_all exact (R.νW :)))
    (fdW := (by with_unfolding_all exact (R.fdW :)))
    (ωY := (by with_unfolding_all exact (R.ωY :)))
    (ωX := (by with_unfolding_all exact (R.ωX :)))
    (ωP := (by with_unfolding_all exact (R.ωP :)))
    (vac := (by with_unfolding_all exact (R.vac :)))
    (vacX := (by with_unfolding_all exact (R.vacX :)))
    (vacP := (by with_unfolding_all exact (R.vacP :)))
    (vY := (by with_unfolding_all exact (R.vY :)))
    (vX := (by with_unfolding_all exact (R.vX :)))
    (vP := (by with_unfolding_all exact (R.vP :)))
    (ItY := (by with_unfolding_all exact (R.ItY :)))
    (ItX := (by with_unfolding_all exact (R.ItX :)))
    (ioY := (by with_unfolding_all exact ((ioYB b R) :)))
    (ioX := (by with_unfolding_all exact ((ioXB b R) :)))
    (Th := (by with_unfolding_all exact (R.Th :)))
    (BV := (by with_unfolding_all exact (R.BV :)))
    (ioP := (by with_unfolding_all exact (R.ioP :)))
    (thF := (by with_unfolding_all exact (R.thF :)))
    (thG := (by with_unfolding_all exact (R.thG :)))
    (nW := (by with_unfolding_all exact (R.nW :)))
    (FW := (by with_unfolding_all exact (R.FW :)))
    (mu := (by with_unfolding_all exact (R.mu :)))
    (twPl := (by with_unfolding_all exact (R.twPl :)))
    (kap := (by with_unfolding_all exact (R.kap :)))
    (lam := (by with_unfolding_all exact (R.lam :)))
    (err0 := (by with_unfolding_all exact (R.err0 :)))

theorem real_ioY {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoYT (@MultT a.D) R) ((R.ioY)) _ (@RealDat.ioY b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoYT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioY :)))).2 :))

theorem real_ioX {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} (R : RealDat a.D A Ks) :
    @HEq (IoXT (@MultT a.D) R) ((R.ioX)) _ (@RealDat.ioX b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R)) :=
  (by with_unfolding_all exact ((castAlong (congrArg (fun m : type_of% (@MultT a.D) => IoXT (@m) R) (multT_eq b a)) ((by with_unfolding_all exact (R.ioX :)))).2 :))

def real3 {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) :
    @RealDat3 b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) :=
  @RealDat3.mk b.D G _ _ Pl0 I0 T (famInThreeCoefficientChange b A) Ks _ _ (alg b iK) ((by with_unfolding_all exact ((real b R.toRealDat) :))) ((by with_unfolding_all exact (R.plI :))) ((by with_unfolding_all exact (R.SF :))) ((by with_unfolding_all exact (R.phs :)))
    ((by with_unfolding_all exact (R.lam3 :)))

end GlobalTheory.Mem.R3.Tr

end
end

