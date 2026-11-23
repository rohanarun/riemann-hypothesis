module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartEq
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0024
public import Formalism.LocalToGlobal.NormalizedHeckeFactors.Bundle0008
public import Formalism.LocalToGlobal.GaloisLevelStructure.TiedRowLoc
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FinTypRepCast
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host
open Formalism.IndefR.RecTie GlobalTheory.RealGeo
open scoped TensorProduct

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

def rowPsi {V : HSp a.D} {n : ℕ} (P : principalLevelFrame.RowPsi V n) : @principalLevelFrame.RowPsi b.D ((V)) n where
  ψ := (by with_unfolding_all exact (P.ψ :))
  inj := (by with_unfolding_all exact (P.inj :))
  into := (by with_unfolding_all exact (P.into :))
  onto := (by with_unfolding_all exact (P.onto :))


variable (a) in
def isotLB : type_of% (@principalLevelFrame.isotL b.D) := @fun V n S θ P M J χ e π =>
  (by with_unfolding_all exact ((@principalLevelFrame.isotL a.D ((V)) n ((S)) ((θ)) (((rowPsi a P))) (((ds a M))) ((J)) ((χ)) ((e)) ((π))) : _))


variable (a) in
theorem isotL_eq : @principalLevelFrame.isotL b.D = @isotLB B C a b := by
  funext V n S θ P M J χ e π
  exact (by with_unfolding_all exact ((congrArg₂ (fun (g : type_of% (@goodPart b.D)) (m : type_of% (@Mult.Mult b.D)) =>
    g θ M J χ e ⊓ principalLevelFrame.isotIn (principalLevelFrame.actM P M) (⨆ N : ℕ, m θ M (principalLevelFrame.levN P (N + 1)) fun _ => 1) π) (goodPart_eq a b) (mult_eq a b)) :))

section General

variable {D : D7} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

def topW (m : type_of% (@MultT D)) (R : RealDat D A Ks) : Prop :=
  ∀ t, LinearMap.range (R.cX.toMap R.prX ∘ₗ (R.HX t).e) = m R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))

abbrev ccJ (m : type_of% (@MultT D)) (R : RealDat D A Ks) (t : T) (j : ℕ) : Submodule ℂ (AmbT (R.MY j)) :=
  m R.θ (R.MY j) (if j < D.R.m then levS _ (R.βY j) (R.datYt t j R.triv) else Set.univ)
    (if j < D.R.m then levChi _ (R.βY j) (R.datYt t j R.triv) else 0)

def ioCW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (y : IoYT (@m) R) (t : T) (k : ℕ) :
    ccJ (@m) R t (k + 1) →ₗ[ℂ] ccJ (@m) R t k :=
  if h : k + 1 < D.R.m then
    (LinearEquiv.ofEq _ _ (by simp only [ccJ, if_pos (show k < D.R.m by omega)])).toLinearMap ∘ₗ
      y t k ∘ₗ (LinearEquiv.ofEq _ _ (by simp only [ccJ, if_pos h])).toLinearMap
  else 0

def ioXW (m : type_of% (@MultT D)) (R : RealDat D A Ks) (x : IoXT (@m) R) (hm : 0 < D.R.m) (hT : topW (@m) R) (t : T) :
    m R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t)) →ₗ[ℂ] ccJ (@m) R t (D.R.m - 1) :=
  (LinearEquiv.ofEq _ _ (by simp only [ccJ, if_pos (show D.R.m - 1 < D.R.m by omega)])).toLinearMap ∘ₗ
    x t ∘ₗ (LinearEquiv.ofEq _ _ (hT t).symm).toLinearMap

def ioOKW (m : type_of% (@MultT D)) (Ch : ChainReal D) (c : Bool) (μ : D.what₂.Tup)
    (y : ∀ k, m Ch.θ (Ch.MY (k + 1)) (Ch.J c μ (k + 1)) (Ch.χ c μ (k + 1)) →ₗ[ℂ] m Ch.θ (Ch.MY k) (Ch.J c μ k) (Ch.χ c μ k))
    (x : m Ch.θ Ch.MX (Ch.JX c μ) (Ch.χX c μ) →ₗ[ℂ] m Ch.θ (Ch.MY (D.R.m - 1)) (Ch.J c μ (D.R.m - 1)) (Ch.χ c μ (D.R.m - 1))) :
    Prop :=
  Lift.IsChainIo (G := fun j => GA D (Ch.Y j)) (D := fun j => ⨂[ℂ] τ, (Ch.MY j).sm τ)
    (fun j => m Ch.θ (Ch.MY j) (Ch.J c μ j) (Ch.χ c μ j)) (D.R.m - 1) (Ch.meas c μ) (Ch.fd μ) (Ch.th μ) (Ch.pt c μ) Ch.It y ∧
  (1 ≤ D.R.m → Lift.IsIo (Ch.measX c μ) (Ch.fdX μ) (Ch.thX μ) (Ch.ptX c μ) Ch.ItX (m Ch.θ Ch.MX (Ch.JX c μ) (Ch.χX c μ))
    (m Ch.θ (Ch.MY (D.R.m - 1)) (Ch.J c μ (D.R.m - 1)) (Ch.χ c μ (D.R.m - 1))) x)

end General

variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section Chain

variable {A : FamIn a.D.what₂.LL G Pl0 T a.D.R.m} {R : RealDat a.D A Ks}

theorem topMult_tr (h : TopMultH R) : letI := alg b iK; TopMultH (real b R) := by
  with_unfolding_all exact (cast (congrArg (fun m : type_of% (@MultT a.D) => topW (@m) R) (multT_eq b a)) h : _)

variable (F : Face a.D A) (tupT : a.D.what₂.Tup → T) (hm : 0 < a.D.R.m) (hTop : TopMultH R)

abbrev chainB : ChainReal b.D :=
  @toChainReal b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) (face b F) ((by with_unfolding_all exact (tupT :))) ((by with_unfolding_all exact (hm :))) (topMult_tr b hTop)

theorem chain_EEc : (toChainReal R F tupT hm hTop).EEc = ((chainB b F tupT hm hTop).EEc) :=
  (by with_unfolding_all exact ((congrArg (fun (g : type_of% (@goodPart a.D)) (c : Bool) =>
    (g R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.levR F c))) (levChi _ (R.βY 0) (R.dat0 (R.levR F c))) R.e0).map
      (PiTensorProduct.lift : MMap (R.MY 0) ≃ₗ[ℂ] AmbT (R.MY 0)).toLinearMap) (goodPart_eq b a)) :))

theorem chain_CC : (toChainReal R F tupT hm hTop).CC = ((chainB b F tupT hm hTop).CC) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ j => m Ch.θ (Ch.MY j) (Ch.J c μ j) (Ch.χ c μ j)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_CCP : (toChainReal R F tupT hm hTop).CCP = ((chainB b F tupT hm hTop).CCP) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ j => m Ch.θ (Ch.MY j) (Ch.JP c μ j) (Ch.χP c μ j)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_CCX : (toChainReal R F tupT hm hTop).CCX = ((chainB b F tupT hm hTop).CCX) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ => m Ch.θ Ch.MX (Ch.JX c μ) (Ch.χX c μ)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_CCXP : (toChainReal R F tupT hm hTop).CCXP = ((chainB b F tupT hm hTop).CCXP) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (Ch : ChainReal a.D) => fun c μ => m Ch.θ Ch.MX (Ch.JXP c μ) (Ch.χXP c μ)) (multT_eq b a) :)
    (toChainReal R F tupT hm hTop)) :))

theorem chain_ioC (t : T) (k : ℕ) (v : AmbT (R.MY (k + 1))) (hv : v ∈ ccJ (@multTB B C b a) R t (k + 1))
    (hv0 : v ∈ ccJ (@MultT a.D) R t (k + 1)) :
    (ioCW (@multTB B C b a) R (ioYB b R) t k ⟨v, hv⟩).1 = (ioCW (@MultT a.D) R ((R.ioY)) t k ⟨v, hv0⟩).1 :=
  (by with_unfolding_all exact ((cast (io_congr R (multT_eq b a) (fun m y _ => ∀ hv : v ∈ ccJ (@m) R t (k + 1),
    (ioCW (@m) R y t k ⟨v, hv⟩).1 = (ioCW (@MultT a.D) R ((R.ioY)) t k ⟨v, hv0⟩).1) ((R.ioY)) ((R.ioX))) (fun _ => rfl) hv) : _))

theorem chain_ioX (t : T) (v : AmbT R.MX) (hT : topW (@multTB B C b a) R)
    (hv : v ∈ multTB b a R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t)))
    (hv0 : v ∈ MultT R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))) :
    (ioXW (@multTB B C b a) R (ioXB b R) hm hT t ⟨v, hv⟩).1 = (ioXW (@MultT a.D) R ((R.ioX)) hm hTop t ⟨v, hv0⟩).1 :=
  (by with_unfolding_all exact ((cast (io_congr R (multT_eq b a) (fun m _ x => ∀ (hT : topW (@m) R)
      (hv : v ∈ m R.θ R.MX (levS _ R.βX (R.datXt t)) (levChi _ R.βX (R.datXt t))),
    (ioXW (@m) R x hm hT t ⟨v, hv⟩).1 = (ioXW (@MultT a.D) R ((R.ioX)) hm hTop t ⟨v, hv0⟩).1) ((R.ioY)) ((R.ioX)))
    (fun _ _ => rfl) hT hv) : _))

theorem chain_ioOK {c : Bool} {μ : a.D.what₂.Tup} (h : (chainB b F tupT hm hTop).IoOK c ((μ))) :
    (toChainReal R F tupT hm hTop).IoOK c μ := by
  have e := io_congr R (multT_eq b a) (fun m y x => ∃ hT : topW (@m) R,
    ioOKW (@m) (toChainReal R F tupT hm hTop) c μ ((by with_unfolding_all exact ((ioCW (@m) R y (tupT μ)) :))) ((by with_unfolding_all exact ((ioXW (@m) R x hm hT (tupT μ)) :))))
    ((by with_unfolding_all exact (R.ioY :))) ((by with_unfolding_all exact (R.ioX :)))
  obtain ⟨_, h'⟩ := cast e.symm (Exists.intro ((by with_unfolding_all exact ((topMult_tr b hTop) :))) ((by with_unfolding_all exact (h :))))
  exact (by with_unfolding_all exact (h' :))

variable (hinj : ∀ i t, Function.Injective (R.extV i t))


include hinj in
theorem inj_tr : letI := alg b iK; ∀ i t, Function.Injective ((real b R).extV i t) := (by with_unfolding_all exact (hinj :))

abbrev liftB : LiftReal b.D (chainB b F tupT hm hTop) :=
  (by with_unfolding_all exact ((@toLiftReal b.D G _ _ Pl0 T (famM b A) Ks _ _ (alg b iK) (real b R) (face b F) ((tupT)) ((hm)) (topMult_tr b hTop)
    (inj_tr b hinj)) : _))

theorem lift_Wc : (toLiftReal R F tupT hm hTop hinj).Wc = ((liftB b F tupT hm hTop hinj).Wc) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (g : type_of% (@goodPart a.D)) (L : LiftReal a.D (toChainReal R F tupT hm hTop)) => fun i =>
    (g R.θ (L.MW i) (L.JW i) (L.χW i) (L.eW i)).map (PiTensorProduct.lift : MMap (L.MW i) ≃ₗ[ℂ] L.AmbW i).toLinearMap)
    (goodPart_eq b a) :) (toLiftReal R F tupT hm hTop hinj)) :))

theorem lift_MultW : (toLiftReal R F tupT hm hTop hinj).MultW = ((liftB b F tupT hm hTop hinj).MultW) :=
  (by with_unfolding_all exact ((congrFun (congrArg (fun (m : type_of% (@MultT a.D)) (L : LiftReal a.D (toChainReal R F tupT hm hTop)) => fun i =>
    m R.θ (L.MW i) (L.JA i) (L.χA i)) (multT_eq b a) :) (toLiftReal R F tupT hm hTop hinj)) :))

end Chain

end GlobalTheory.Mem.R3.Tr

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyAllIff
section
noncomputable section

namespace GlobalTheory.HeightCounting

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain _root_.Formalism.L2 Formalism.L2.NT


set_option synthInstance.maxHeartbeats 400000 in
structure NAllC (D : D7) (C : NChoice D) where
  gal : NGalTied D
  n : NormalizedHeckeDataPlaceholder D
  loc : LocTied D
  data : NormalizedDataCompatibility D
  cover : NormalizedLocalCompatibility D gal.mt
  chiD : NC.NChiData D
  chi : NC.NormalizedCharacterCompatibility D chiD
  rho : NR.NRhoTied D
  types : NormalizedTypesCompatibility D gal.fr.jE
  twF : TwFrame D
  tw : NTwTied D twF
  nct : NChTie D C
  exp : NExpTied D
  choice : ChoiceC D C
  eMt_level : ∀ (w : D.what₂.places.Pl) (j : ℕ) (h1 : 1 ≤ j) (h2 : j ≤ D.R.m)
    (hw : TwistedAt D w) (hA : NX.AdmTw D (C.twI w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w)))),
    ∃ ι : FractionRing (C.Oe w) →+* ℂ, (∀ x : D.what₂.LL, ι (C.embW w x) = D.what₂.embLL x) ∧
      (gal.mt (D.what₂.muTw w) j h1 h2).J =
        (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w) ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J ∧
      ∀ (κ : Formalism.AUTREP.GAf D.host.E D.R.nV) (h : κ ∈ (gal.mt (D.what₂.muTw w) j h1 h2).J)
        (h' : κ ∈ (exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
          ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).J),
        (((gal.mt (D.what₂.muTw w) j h1 h2).χ ⟨κ, h⟩ : ℂˣ) : ℂ) =
          ι (C.kMapE w (((exp.mtV (C.twI w) j (C.sd w) (C.k' w) (C.Q w)
            ((C.psi' w).comp (D.ntw.art (C.twI w) (C.Q w))) h1 h2 hA).χ ⟨κ, h'⟩ : (NX.Kk D (C.twI w) (C.k' w))ˣ) :
              NX.Kk D (C.twI w) (C.k' w)))
  cf : Host.CharFrame D
  tp : Host.TupTied D cf C
  tupLink : gal.TupLink tp
  eta_eq : ∀ x, chiD.etaT.χ x = cf.eta.1 x
  ringSpec_normalisedCharacter_eq : ∀ (j : Fin D.R.m) x, (chiD.mu0 (j.1 + 1)).χ x = (cf.mu0 j).1 x
  del_eq : ∀ s x, (chiD.del s).χ x = (cf.delAt (D.ntw.l s)).1 x
  psi_eq : ∀ a x, (chiD.psi a).χ x = (tp.psi (D.nd.w a)).1 x
  plB : D.what₂.places.Pl → ValuationSubring ℂ
  plκ : ∀ w, haveI : Fact (D.what₂.places.resChar w).Prime := ⟨D.what₂.places.resChar_prime w⟩
    IsLocalRing.ResidueField (plB w) ≃+* Formalism.CyclotomicNorms.Fbar (D.what₂.places.resChar w)
  plB_loc : ∀ (i : D.nd.Loc) (y : D.nd.O i),
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    ∃ h : iotaOC D i y ∈ plB (D.nd.w i),
      Formalism.MainNotions.N.fbCast (D.nd.w_l i) (D.what₂.places.resChar_prime (D.nd.w i)) (D.nd.lPrime i).out
        (plκ (D.nd.w i) (IsLocalRing.residue (plB (D.nd.w i)) ⟨_, h⟩)) =
        D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) y)
  plB_iota : ∀ (i : D.nd.Loc) k v x,
    haveI : Fact (D.what₂.places.resChar (D.nd.w i)).Prime := ⟨D.what₂.places.resChar_prime (D.nd.w i)⟩
    D.ntypes.iota k v (D.nd.w i) x = redThrough (plB (D.nd.w i)) (plκ (D.nd.w i)) (D.ntypes.teichC k x)
  etaT_link : ∀ (w : PlE D.host) (α : ℂ), chiD.etaT.At w α →
    D.naut.frobEig (D.naut.locG D.naut.etaT w) = {α⁻¹}
  muC_link : ∀ i : D.nd.Loc, ∀ᶠ w in Filter.cofinite, ∀ α : ℂ,
    (chiD.mu0 (D.nd.j i) * chiD.del (D.ntw.twOf i) * chiD.psi i).At w α →
    D.naut.frobEig (D.naut.locG (D.naut.muC i) w) = {α⁻¹}
  iCq_embO : ∀ s (x : ↥D.LL0), twF.iCq s (chiD.embO s true x) = D.what₂.embLL (x : D.what₂.LL)
  embO_star : ∀ s (x y : ↥D.LL0), (y : D.what₂.LL) = star (x : D.what₂.LL) → chiD.embO s false x = chiD.embO s true y

def GoodCl (D : D7) (C : NChoice D) (I : TwIn D) : Prop :=
  ∀ w, TwistedAt D w →
    (Formalism.MainNotions.IntegralHeckeEveryConjugate D (BlochKatoReduction.bk0 D) I.E I.N0 ∧ D.ntw.NonzeroIndexPlace (C.twI w) ∧ BlochKatoReduction.Gen.SetHyp (BlochKatoReduction.bk0 D) (C.twI w) ∧ I.Ok (C.twI w)) →
    ExpGood D I (avD D (avDesign D) (C.twI w)) (C.twI w) ⟨C.Q w, C.k' w, BlochKatoReduction.Gen.psiAt (C.sd w) (C.psi' w)⟩

variable {D : D7} {C : NChoice D} {I : TwIn D}

def NAllC.toAll (A : NAllC D C) (h : GoodCl D C I) : NormalizedTwistCompatibility D C I :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, h, A.choice.conj⟩ }

def NAllC.ofAll (A : NormalizedTwistCompatibility D C I) : NAllC D C :=
  { A with
    choice := ⟨A.choice.twI_conj, A.choice.sd_place, A.choice.emb_side, A.choice.sd_conj, A.choice.one, A.choice.conj⟩ }

theorem goodCl_of_all (A : NormalizedTwistCompatibility D C I) : GoodCl D C I := A.choice.good

end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2 Formalism.L2.Host NumberField IsDedekindDomain

structure PhtOn {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} (Wd : WDSide D T) (fr : OmFrame D)
    (p : ∀ (l : ℕ) [Fact l.Prime] (a : ℕ), (G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) → Prop) : Prop where
  card : ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (τ : D.host.E →+* Qbar l) (w : PlE D.host), p l a r →
    (∀ x : 𝓞 D.host.E, x ∈ w.asIdeal ↔ ‖τ (x : D.host.E)‖ < 1) → Wd.IsdRW l ι r w → Multiset.card (Wd.jumpsW l ι r τ) = a

def PhtCmp : Prop :=
  ∀ (D : D7) (fr : OmFrame D) (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (Wd : WDSide D T), PhtOn Wd fr fun l _ a r =>
    Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))

end GlobalTheory.HeightCounting

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Wp3ApplyEqSqMulSubSqMul
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Lev Formalism.L2.Pj Formalism.L2.Host

namespace GlobalTheory.Mem.R3.Tr

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {C : Cols B} {a : Late B C} (b : Late B C) {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
variable {Ks : Type} [Field Ks] [NumberField Ks] [iK : Algebra Ks a.D.what₂.LL]

section General

variable {D : D7} {A : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

abbrev Parts (R : RealDat3 D A Ks) : Type :=
  (A.fam3.base3.Ix → Submodule ℂ R.HE.H) × (LevelP R.Pg D.R.r ℂ → Submodule ℂ (MMap (R.MY 0))) ×
    ∀ i : Fin D.R.m, A.fam3.base3.Ix → Submodule ℂ (R.HW i (sg0 D A.A)).H

def cxW (R : RealDat3 D A Ks) (F : Face3 D A) (u : Parts R) : Cx.CxData A.fam3.amb3 :=
  { R.toCx3 F with
    EEp := fun p => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) (u.1 p)) :))
    EEl := fun c => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) ((u.2.1 (R.toRealDat.levR F.lv2 c)).comap R.HE.e)) :))
    Wp := fun i p => (by with_unfolding_all exact ((Tw.sub (twAt D.what₂.embLL A.A.v0) (u.2.2 i p)) :)) }

def carriesW (R : RealDat3 D A Ks) (E : type_of% R.EEc) (p : A.fam3.base3.Ix) (c : Pl D.host.E → List ℤ → ℂ) : Prop :=
  E c ≠ ⊥ ∧ (E c).map (LinearMap.adjoint (R.Th A.A.μ0)) ≤
    Submodule.span ℂ (R.jX A.A.μ0 '' ((A.rowI A.A.μ0).inertTypeEigenspaceSum p.1 : Set (A.A.fam.R A.A.μ0).S.Forms))

def trSemW (R : RealDat3 D A Ks) (F : Face3 D A) (u : type_of% R.Carries × type_of% R.Wc')
    (tr : Fin D.R.m → (I0 × List ℕ → D.what₂.LL) → I0 × List ℕ → D.what₂.LL) : Prop :=
  ∀ j p c, u.1 p c → ∀ s : (A.liftI j A.A.μ0).OpIx → D.what₂.LL,
    (∃ x : (A.A.fam.L j A.A.μ0).S.Forms, x ∈ Cx.BlockGood.goodR (A.A.fam.L j A.A.μ0) (A.A.fam.lvlA F.P0 F.ψ0) ∧
      (∀ i, (A.liftI j A.A.μ0).opAll i x = s i • x) ∧ R.thG j A.A.μ0 (R.jV j A.A.μ0 x) ∈ u.2 j c ∧
      R.thG j A.A.μ0 (R.jV j A.A.μ0 x) ≠ 0) →
    ∀ k : (A.liftI j A.A.μ0).PlI × List ℕ, s (Sum.inr k) = tr j p.1.2 ((A.liftI j A.A.μ0).plI k.1, k.2)

def partAtW (F : Face3 D A) (X : Cx.CxData A.fam3.amb3) (i : Fin D.R.m) (p : A.fam3.base3.Ix) (v : InfinitePlace D.what₂.LL) : Prop :=
  ∃ x, X.tC F.cr false i A.A.μ0 (Cx.cpt A.A.v0.embedding x) ∈ X.Wp i p ∧
    Formalism.HermitianLatticesTheory.majAt (Pi.basisFun D.what₂.LL _) ((Cx.lv (F.fc X.zs) false).XT i A.A.μ0) v x x ≠ 0

end General

section Three

variable {A : FamIn3 a.D.what₂.LL G Pl0 I0 (List ℕ) T a.D.R.m} (R : RealDat3 a.D A Ks) (F : Face3 a.D A)

theorem eec_eq : R.EEc = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEc) :)) :=
  (by with_unfolding_all exact ((congrArg (fun (m : type_of% (@partFull a.D)) (c : Pl a.D.host.E → List ℤ → ℂ) =>
    (m R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 R.triv)) (levChi _ (R.βY 0) (R.dat0 R.triv)) R.SF fun P d => c P (dualLab d)).comap
      R.HE.e) (partFull_eq b a)) :))

theorem wc_eq : R.Wc' = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wc') :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (W : type_of% R.toRealDat.Wat) (m : type_of% (@partFull a.D)) (i : Fin a.D.R.m)
      (c : Pl a.D.host.E → List ℤ → ℂ) =>
    (W i (sg0 a.D A.A) R.triv ⊓
      m R.θ (R.MW i (sg0 a.D A.A)) (levS _ (R.βW i) (R.datWp i R.triv)) (levChi _ (R.βW i) (R.datWp i R.triv)) R.SF c).comap
      (R.HW i _).e) (wat_eq b R.toRealDat) (partFull_eq b a)) :))

theorem carries_eq : R.Carries = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Carries) :)) :=
  (by with_unfolding_all exact ((congrArg (carriesW R) (eec_eq b R)) :))

theorem realAdelicInertTransport_typeRows_eq : R.EEp3 = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEp3) :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (Q : type_of% R.Carries) (E : type_of% R.EEc) (p : A.fam3.base3.Ix) =>
    ⨆ (c : Pl a.D.host.E → List ℤ → ℂ) (_ : Q p c), E c) (carries_eq b R) (eec_eq b R)) :))

theorem wp3_apply_eq_sq_mul_sub_sq_mul : R.Wp3 = (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wp3) :)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun (Q : type_of% R.Carries) (E : type_of% R.Wc') (i : Fin a.D.R.m) (p : A.fam3.base3.Ix) =>
    ⨆ (c : Pl a.D.host.E → List ℤ → ℂ) (_ : Q p c), E i c) (carries_eq b R) (wc_eq b R)) :))

theorem parts_eq (_F : Face3 a.D A) : ((R.EEp3, R.toRealDat.EEat, R.Wp3) : Parts R) =
    ((by with_unfolding_all exact ((letI := alg b iK; (real3 b R).EEp3) :)), (by with_unfolding_all exact ((letI := alg b iK; (real b R.toRealDat).EEat) :)), (by with_unfolding_all exact ((letI := alg b iK; (real3 b R).Wp3) :))) :=
  (by with_unfolding_all exact ((Prod.ext (realAdelicInertTransport_typeRows_eq b R) (Prod.ext (eeat_eq b R.toRealDat) (wp3_apply_eq_sq_mul_sub_sq_mul b R)) :
    ((R.EEp3, R.toRealDat.EEat, R.Wp3) : Parts R) = (_, _, _)) :))

theorem toCx3_eq : R.toCx3 F = (@RealDat3.toCx3 (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 I0 T (@famInThreeCoefficientChange B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R) (@face3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A F)) :=
  (by with_unfolding_all exact ((congrArg (cxW R F) (parts_eq b R F)) :))

theorem trISem_eq : R.TrISem F = (@RealDat3.TrISem (@Late.D B C b) G ‹Group G› ‹Fintype G› Pl0 I0 T (@famInThreeCoefficientChange B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A) Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› (@alg B C a b Ks ‹Field Ks› iK) (@real3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T Ks ‹Field Ks› ‹@NumberField Ks ‹Field Ks›› iK A R) (@face3 B C a b G ‹Group G› ‹Fintype G› Pl0 I0 T A F)) :=
  (by with_unfolding_all exact ((congrArg₂ (fun Q E => trSemW R F (Q, E)) (carries_eq b R) (wc_eq b R)) :))

variable {R F}

theorem isInert_tr (h : R.IsInert) : letI := alg b iK; (real3 b R).IsInert := by
  letI := alg b iK
  constructor
  case tie =>
    constructor
    · exact (by with_unfolding_all exact (h.tie.plI_inj :))
    · exact (by with_unfolding_all exact (h.tie.okI :))
  case onto => exact (by with_unfolding_all exact (h.onto :))
  case hR => exact (by with_unfolding_all exact (h.hR :))
  case hL => exact (by with_unfolding_all exact (h.hL :))
  case SF => exact (by with_unfolding_all exact (h.SF :))

theorem isTup_tr (h : R.IsTup) : letI := alg b iK; (real3 b R).IsTup := by
  letI := alg b iK
  constructor
  case mu_off => exact (by with_unfolding_all exact (h.mu_off :))
  case mu_used => exact (by with_unfolding_all exact (h.mu_used :))
  case mu_ne => exact (by with_unfolding_all exact (h.mu_ne :))
  case mu_conj => exact (by with_unfolding_all exact (h.mu_conj :))
  case mu_on => exact (by with_unfolding_all exact (h.mu_on :))

theorem isScal_tr (h : R.IsScal F) : letI := alg b iK; (real3 b R).IsScal (face3 b F) := by
  letI := alg b iK
  constructor
  case lam0 => exact (by exact ((Eq.mp (congrArg (fun W : type_of% R.Wp3 => ∀ i t p (l : ℝ), W i p ≠ ⊥ →
      (∀ x ∈ W i p, R.thG i t (LinearMap.adjoint (R.thG i t) x) = (l : ℂ) • x) → R.lam3 i t p A.A.v0 = l) (wp3_apply_eq_sq_mul_sub_sq_mul b R)) h.lam0) :))
  case kap => exact (by exact ((Eq.mp (congrArg (fun E : type_of% R.EEp3 => ∀ κ : ℝ,
      Lift.IsKap a.D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) E R.lamN κ →
      (∃ t p, E p ≠ ⊥ ∧ ∏ j ∈ Finset.Icc 1 a.D.R.m, R.lamN t j p ≠ 0) → R.kap = κ) (realAdelicInertTransport_typeRows_eq b R)) h.kap) :))
  case off => exact (by exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => ∀ i p v (l : ℝ), v ≠ A.A.v0 → partAtW F X i p v →
      (∀ x, X.tC F.cr false i A.A.μ0 (Cx.cpt A.A.v0.embedding x) ∈ X.Wp i p → ∀ y,
        inner ℂ (X.wC false i v (Cx.cpt v.embedding ((X.liftMat F.cr false i A.A.μ0).mulVec x)))
            (X.wC false i v (Cx.cpt v.embedding ((X.liftMat F.cr false i A.A.μ0).mulVec y))) =
          ((l : ℝ) : ℂ) * Formalism.HermitianLatticesTheory.majAt (Pi.basisFun a.D.what₂.LL _) ((Cx.lv (F.fc X.zs) false).XT i A.A.μ0) v x y) →
      R.lam3 i A.A.μ0 p v = l) (toCx3_eq b R F)) h.off) :))
  case abs0 => exact (by exact ((Eq.mp (congrArg (fun u : Parts R => ∀ i t p, u.2.2 i p = ⊥ →
      R.lam3 i t p A.A.v0 = Real.exp ((F.Zsc (cxW R F u).zs).l6m i)) (parts_eq b R F)) h.abs0) :))
  case abs => exact (by exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => ∀ i p v, v ≠ A.A.v0 → ¬ partAtW F X i p v →
      R.lam3 i A.A.μ0 p v = Real.exp ((F.Zsc X.zs).l6m i)) (toCx3_eq b R F)) h.abs) :))
  case tup => exact (by with_unfolding_all exact (h.tup :))

theorem primRows3_tr (h : PrimRows3 R F) : letI := alg b iK; PrimRows3 (real3 b R) (face3 b F) := by
  set_option maxHeartbeats 16000000 in
   letI := alg b iK
   constructor
   case heckeR => exact (by with_unfolding_all exact (h.heckeR :))
   case heckeL => exact (by with_unfolding_all exact (h.heckeL :))
   case hecke => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => (∃ hE, Cx.HeckeIntertwiningDefinite A X hE) ∧ ∃ hW, Cx.HeckeIntertwiningLifts A X hW) (toCx3_eq b R F)) h.hecke) :))
   case gUnit => exact (by with_unfolding_all exact (h.gUnit :))
   case gEquiv => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun u : Parts R => Cx.GEquiv3 A (cxW R F u) (R.gEx F) ∧ Cx.LiftGroupEquivariance A (cxW R F u) (R.gWx F)) (parts_eq b R F)) h.gEquiv) :))
   case block => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => X.zs.InBlock) (toCx3_eq b R F)) h.block) :))
   case rowTest => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.RowTest X) (toCx3_eq b R F)) h.rowTest) :))
   case liftTest => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTest X) (toCx3_eq b R F)) h.liftTest) :))
   case liftTestB => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => Rat.LiftTestB X false) (toCx3_eq b R F)) h.liftTestB) :))
   case liftOnto => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => ∀ hW, Cx.HeckeIntertwiningLifts A X hW →
      U2.OntoC A X F.P0 F.ψ0 F.P1 F.ψ1 hW) (toCx3_eq b R F)) h.liftOnto) :))
   case pos => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => ∀ c, (Cx.lv (F.fc X.zs) c).Pos) (toCx3_eq b R F)) h.pos) :))
   case posScal => exact (by with_unfolding_all exact (h.posScal :))
   case levE => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun u : Parts R =>
      Cx.LevType3 A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) false F.P0 F.ψ0 ∧
      Cx.LevType3 A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gEx F) true F.P1 F.ψ1) (parts_eq b R F)) h.levE) :))
   case h2P => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 =>
      Cx.PrincipalLevelBijectivity A X (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc)) (toCx3_eq b R F)) h.h2P) :))
   case thmB => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun E : type_of% R.EEp3 =>
      Lift.IsKap a.D.R.m (fun t => R.Th t ∘ₗ LinearMap.adjoint (R.Th t)) E R.lamN R.kap) (realAdelicInertTransport_typeRows_eq b R)) h.thmB) :))
   case sumE => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => ∀ c, X.PartsE c) (toCx3_eq b R F)) h.sumE) :))
   case unif => exact (by with_unfolding_all exact (h.unif :))
   case mLat => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => X.MLat false) (toCx3_eq b R F)) h.mLat) :))
   case levW => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun u : Parts R =>
      Cx.LevelTypeOfLifts A (cxW R F u) (P1 := F.P1) (ψ1 := F.ψ1) (Dc := F.Dc) (Sp := F.Sp) (Zsc := F.Zsc) (R.gWx F) false F.P0 F.ψ0) (parts_eq b R F)) h.levW) :))
   case thmA => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun W : type_of% R.Wp3 => ∀ i t,
      Lift.IsLamP (R.thG i t) (LinearMap.adjoint (R.thG i t)) (W i) fun p => R.lam3 i t p A.A.v0) (wp3_apply_eq_sq_mul_sub_sq_mul b R)) h.thmA) :))
   case sumW => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => X.PartsW false) (toCx3_eq b R F)) h.sumW) :))
   case scalConj => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => X.GalD F.cr false) (toCx3_eq b R F)) h.scalConj) :))
   case dimParts => exact (by with_unfolding_all exact ((Eq.mp (congrArg (fun X : Cx.CxData A.fam3.amb3 => X.DimParts false) (toCx3_eq b R F)) h.dimParts) :))

theorem realAdelicInertTransport_furtherRows (h : UnusedChoiceStatements R F) : letI := alg b iK; UnusedChoiceStatements (real3 b R) (face3 b F) := by
  letI := alg b iK
  constructor
  case ex => exact (by with_unfolding_all exact ((exAt_tr b h.ex) :))
  case conj => exact (by with_unfolding_all exact (h.conj :))
  case levelW => exact (by with_unfolding_all exact ((lLevelW_tr b h.levelW) :))
  case integral => exact (by with_unfolding_all exact (h.integral :))

end Three

end GlobalTheory.Mem.R3.Tr

end
end

