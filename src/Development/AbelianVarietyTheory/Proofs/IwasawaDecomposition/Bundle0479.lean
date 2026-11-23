module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0473
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0466

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemilinearFormsLiftSameComplexValues
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.DefLatBC.LiftExt


open _root_.Formalism.L2.Col in
set_option maxHeartbeats 1000000 in
private theorem liftHom_reidx (X : Fields) {L : Type} [Field L] [NumberField L] [StarRing L] (ι : X.K →+* L)
    (e : X.Tau → X.E →+* L) (he : ∀ τ, ι.comp (X.emb τ) = e τ) {n : ℕ} (lam₁ lam₂ : X.Tau → DomWeight n)
    (hl : lam₂ = lam₁) {SG₁ SG₂ : Finset (HeightOneSpectrum (𝓞 X.E))} (hS : SG₂ = SG₁)
    (Λ₁ : LevFam X.E X.K n SG₁) (Λ₂ : LevFam X.E L n SG₂)
    (hΛ : ∀ (w : ↥SG₁) (hw : w.1 ∈ SG₂), Λ₂ ⟨w.1, hw⟩ = (Λ₁ w).coefMap ι)
    (c₁ : X.K →+* ℂ) (c₂ : L →+* ℂ) (hc : ∀ x, c₂ (ι x) = c₁ x) :
    ∃ Lf : (formGSD (roundPk X lam₁ fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun →+
      (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₂
          fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₂) => d.1.N) Λ₂).EqFun,
      (∀ (a : X.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d₁ d₂, HEq d₂ d₁ → HEq (MvPolynomial.map c₂ ((Lf ψ).1 d₂).1) (MvPolynomial.map c₁ (ψ.1 d₁).1) := by
  subst lam₂
  subst SG₂
  have hΛ' : Λ₂ = Λ₁.coefMap ι := funext fun w => hΛ w w.2
  subst hΛ'
  have hmem : ∀ ψ : (formGSD (roundPk X lam₁ fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) Λ₁).EqFun,
      (fun d => hfsJ ι lam₁ (ψ.1 d)) ∈ (formGSD (X := ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields))
        (roundPk ({F := X.F, E := X.E, K := L, Tau := X.Tau, emb := e} : Fields) lam₁
          fun d : DecoSet (E := X.E) (n := n) (ST := ∅) (SG := SG₁) => d.1.N) (Λ₁.coefMap ι)).EqFun := by
    intro ψ
    obtain ⟨φ₂, h⟩ := GlobalTheory.Mem.R3.Tr.levelFamily_coefficientChange_liftRound X ι e he lam₁ Λ₁ (Λ₁.coefMap ι) (fun w => rfl)
      (fun w h₁ h₂ hh => by
        have : h₁ = h₂ := Subtype.ext hh
        subst this
        rfl) ψ
    have : (fun d => hfsJ ι lam₁ (ψ.1 d)) = φ₂.1 := funext fun d => Subtype.ext (h d).symm
    rw [this]
    exact φ₂.2
  refine ⟨{ toFun := fun ψ => ⟨fun d => hfsJ ι lam₁ (ψ.1 d), hmem ψ⟩, map_zero' := ?_, map_add' := ?_ }, ?_, ?_⟩
  · apply Subtype.ext
    funext d
    exact map_zero _
  · intro ψ χ
    apply Subtype.ext
    funext d
    exact map_add _ _ _
  · intro a ψ
    apply Subtype.ext
    funext d
    exact hfsJ_smul ι lam₁ a (ψ.1 d)
  · intro ψ d₁ d₂ hd
    cases hd
    apply heq_of_eq
    show MvPolynomial.map c₂ (MvPolynomial.map ι (ψ.1 d₁).1) = _
    rw [MvPolynomial.map_map]
    have hc' : c₂.comp ι = c₁ := RingHom.ext hc
    rw [hc']


open _root_.Formalism.L2.Col in
private theorem formsLift_of_eqFunLift {K₁ K₂ : Type} [Field K₁] [NumberField K₁] [StarRing K₁] [Field K₂] [NumberField K₂] [StarRing K₂]
    (ι : K₁ →+* K₂) (S₁ : GSD K₁) (S₂ : GSD K₂) (h₁ : S₁.Ok) (h₂ : S₂.Ok) (Lf : S₁.EqFun →+ S₂.EqFun)
    (hLf : ∀ (a : K₁) ψ, Lf (a • ψ) = ι a • Lf ψ) :
    ∃ L : (S₁.toCSD h₁).Forms →+ (S₂.toCSD h₂).Forms, (∀ (a : K₁) f, L (a • f) = ι a • L f) ∧
      ∀ f, (S₂.res h₂).symm (L f) = Lf ((S₁.res h₁).symm f) := by
  refine ⟨(S₂.res h₂).toLinearMap.toAddMonoidHom.comp (Lf.comp (S₁.res h₁).symm.toLinearMap.toAddMonoidHom),
    fun a f => ?_, fun f => ?_⟩
  · show S₂.res h₂ (Lf ((S₁.res h₁).symm (a • f))) = ι a • S₂.res h₂ (Lf ((S₁.res h₁).symm f))
    rw [map_smul, hLf, map_smul]
  · show (S₂.res h₂).symm (S₂.res h₂ (Lf ((S₁.res h₁).symm f))) = _
    exact LinearEquiv.symm_apply_apply _ _


set_option maxHeartbeats 4000000 in
private theorem eqFun_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x) :
    ∃ Lf : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).EqFun →+ (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').EqFun,
      (∀ (a : B.fields.K) ψ, Lf (a • ψ) = ι a • Lf ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((Lf ψ).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (ψ.1 d).1) := by
  subst hj
  cases B with | mk P₁ =>
  cases B' with | mk P₂ =>
  dsimp only at hpre
  subst hpre
  have ef : f' = f := eq_of_heq hf
  have ep : w'.px = w.px := eq_of_heq hpx
  have hv : ((baseOfColW w').primes w'.px).vGs = ((baseOfColW w).primes w.px).vGs := by
    rw [ep]
    rfl
  have hι' : ∀ x, (baseOfColW w').embLL (ι x) = (baseOfColW w).embLL x := hι
  refine liftHom_reidx (baseOfColW w).fields ι (baseOfColW w').tauLL ?_ _ _ rfl ?_ _ _ ?_ (baseOfColW w).embLL
    (baseOfColW w').embLL hι
  · intro τ
    ext x
    apply (baseOfColW w').embLL.injective
    have h1 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w) τ)
    have h2 := congrArg (fun g => g x) (Base.fields_embC (baseOfColW w') τ)
    simp only [Formalism.L2.Col.Fields.embC, RingHom.comp_apply] at h1 h2
    exact (hι' _).trans (h1.trans h2.symm)
  · exact (rowLevelPrimes_colTuples_eq_vGs w' W').trans (hv.trans (rowLevelPrimes_colTuples_eq_vGs w W).symm)
  · refine glue_inv_coefMap_of_empty ι (twistRamifiedPrimes_empty_colTuples w W) (twistRamifiedPrimes_empty_colTuples w' W') _ _ _ _ ?_
    intro p hp
    refine levKV_coefMap_of ι p.1 (fun s => w.I.Ch.chi s p) (fun s => w'.I.Ch.chi s ⟨p.1, hp⟩) ?_ _ _ _ _
    intro s c
    apply (baseOfColW w').embLL.injective
    refine Eq.trans ?_ (hι' _).symm
    obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (c : 𝓞 (baseOfColW w).fields.E ⧸ p.1.asIdeal)
    have hy0 : ((y : 𝓞 (baseOfColW w).fields.E) : (baseOfColW w).fields.E) ≠ 0 := by
      intro h0
      have h0' : y = 0 := RingOfIntegers.coe_injective (h0.trans (by simp))
      rw [h0', map_zero] at hy
      exact c.ne_zero hy.symm
    have e1 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w' s ⟨p.1, hp⟩ c y (Units.mk0 _ hy0) rfl hy.symm
    have e2 := GlobalTheory.Mem.R3.Rw.ChiTr.embLL_chi w s p c y (Units.mk0 _ hy0) rfl hy.symm
    have eC : w'.I.C = w.I.C := w'.C_eq.trans (ef.trans w.C_eq.symm)
    rw [eC] at e1
    exact e1.trans e2.symm


set_option maxHeartbeats 4000000 in
private theorem forms_lift {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} (w : ColW B f T)
    (w' : ColW B' f' T') (W : Set B.places.Pl) (W' : Set B'.places.Pl) (hpre : B'.toPre = B.toPre) (hf : HEq f' f)
    (hpx : HEq w'.px w.px) (j j' : ℕ) (hj : j = j') (ι : B.fields.K →+* B'.fields.K) (hι : ∀ x, B'.embLL (ι x) = B.embLL x)
    (h₁ : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T W))).1 j).Ok) (h₂ : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' W'))).1 j').Ok) :
    ∃ L : (Formalism.L2.Col.GSD.toCSD _ h₁).Forms →+ (Formalism.L2.Col.GSD.toCSD _ h₂).Forms,
      (∀ (a : B.fields.K) ψ, L (a • ψ) = ι a • L ψ) ∧
      ∀ ψ d d', HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₂).symm (L ψ)).1 d').1)
        (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) (((Formalism.L2.Col.GSD.res _ h₁).symm ψ).1 d).1) := by
  obtain ⟨Lf, hs, hc⟩ := eqFun_lift w w' W W' hpre hf hpx j j' hj ι hι
  obtain ⟨L, hL, hr⟩ := formsLift_of_eqFunLift ι _ _ h₁ h₂ Lf hs
  refine ⟨L, hL, fun ψ d d' hd => ?_⟩
  rw [hr]
  exact hc _ d d' hd

end GlobalTheory.Mem.R3.DefLatBC.LiftExt

set_option maxHeartbeats 4000000 in
theorem _root_.GlobalTheory.T.exists_semilinearFormsLift_sameComplexValues : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ L : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms →+ ((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).fam3.F.L j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0).S.Forms, (∀ (a : (w.st Z).toD7.what₂.LL) (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms), L (a • f) = φ a • L f) ∧ (∀ (f : ((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).fam3.F.L j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0).S.Forms) (d : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D) (d' : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D), HEq d' d → HEq (MvPolynomial.map (B'.embLL : B'.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))).symm (L f) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 ((j' : ℕ) + 1)).V) d').1) (MvPolynomial.map (B.embLL : B.fields.K →+* ℂ) ((((((Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).res (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))).symm f : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).EqFun)) : (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).D → (Formalism.L2.Col.mtKGSD (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 ((j : ℕ) + 1)).V) d).1))) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hp Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ _ j j' hj φ hφ => ?_
  exact GlobalTheory.Mem.R3.DefLatBC.LiftExt.forms_lift w w' Wt {v | B'.places.resChar v ∈ T'.pl} hE.1 hf hp ((j : ℕ) + 1) ((j' : ℕ) + 1)
    (by rw [hj]) φ hφ
    (Formalism.L2.Col.mtKOk (Pr := B.primes w.px) B.wts w.I.Ch w.I.sel (mu0F (X := B.fields) (tuOf w.I (usedOf w.I T Wt))).1 hX ((j : ℕ) + 1))
    (Formalism.L2.Col.mtKOk (Pr := B'.primes w'.px) B'.wts w'.I.Ch w'.I.sel (mu0F (X := B'.fields) (tuOf w'.I (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}))).1 hX' ((j' : ℕ) + 1))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.NonlocalTrait

theorem exists_common_ext {F L₁ L₂ : Type} [Field F] [Field L₁] [Field L₂] (a : F →+* L₁) (b : F →+* L₂) :
    ∃ (L : Type) (_ : Field L) (i : L₁ →+* L) (j : L₂ →+* L), i.comp a = j.comp b := by
  letI := a.toAlgebra
  letI := b.toAlgebra
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (TensorProduct F L₁ L₂)
  letI := Ideal.Quotient.field m
  refine ⟨TensorProduct F L₁ L₂ ⧸ m, inferInstance,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := F) (A := L₁) (B := L₂)).toRingHom, ?_⟩
  rw [RingHom.comp_assoc, RingHom.comp_assoc]
  congr 1
  exact Algebra.TensorProduct.includeLeftRingHom_comp_algebraMap

theorem torusExtension_iterate {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G))) :
    Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G))) := by
  obtain ⟨T⟩ := h
  exact ⟨torusExtOfIso (pullCompIso b a G) T⟩

theorem torusExtension_compose {K : Type} [Field K] {S S₁ : Scheme.{0}} (a : S₁ ⟶ S)
    (b : Spec (CommRingCat.of K) ⟶ S₁) (G : Over S) [GrpObj G]
    (h : Nonempty (TorusExtension ((Over.pullback b).obj ((Over.pullback a).obj G)))) :
    Nonempty (TorusExtension ((Over.pullback (b ≫ a)).obj G)) := by
  obtain ⟨T⟩ := h
  haveI : IsMonHom (pullCompIso b a G).symm.hom := inferInstanceAs (IsMonHom (pullCompIso b a G).inv)
  exact ⟨torusExtOfIso (pullCompIso b a G).symm T⟩

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (h : B →+* C) :
    spMap (h.comp f) = spMap h ≫ spMap f := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

end GlobalTheory.NonlocalTrait


open GlobalTheory.NonlocalTrait in
theorem GlobalTheory.exists_trait_nonlocal_torusExtension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (G : Over (Sp R)) [GrpObj G], IsSemiAbelian G →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (g : R →+* W), ¬ IsLocalHom g →
    ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsDiscreteValuationRing V) (ψ : R →+* V)
      (Ω : Type) (_ : Field Ω) (α : FractionRing V →+* Ω) (β : W →+* Ω),
      IsLocalHom ψ ∧ (∀ x ∈ maximalIdeal W, β x = 0) ∧
      (α.comp (algebraMap V (FractionRing V))).comp ψ = β.comp g ∧
      Nonempty (TorusExtension ((Over.pullback (spMap ((algebraMap V (FractionRing V)).comp ψ))).obj G)) := by
  intro R _ _ _ _ G _ hG W _ _ g hg
  set p : Ideal R := Ideal.comap g (maximalIdeal W) with hp
  haveI : p.IsPrime := Ideal.comap_isPrime g (maximalIdeal W)
  obtain ⟨r₀, hr₀u, hr₀⟩ : ∃ r, IsUnit (g r) ∧ ¬ IsUnit r := by
    by_contra h
    push_neg at h
    exact hg ⟨fun r hr => h r hr⟩
  have hr₀p : r₀ ∉ p := fun h => ((mem_maximalIdeal _).1 (Ideal.mem_comap.1 h)) hr₀u
  have hpm : p ≤ maximalIdeal R := le_maximalIdeal (Ideal.IsPrime.ne_top inferInstance)
  haveI : IsLocalRing (R ⧸ p) := .of_surjective' (Ideal.Quotient.mk p) Ideal.Quotient.mk_surjective
  have hunit : ∀ r : R, IsUnit (Ideal.Quotient.mk p r) → IsUnit r := by
    intro r hr
    obtain ⟨b, hb⟩ := hr.exists_right_inv
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective b
    by_contra hru
    have h1 : r * y ∈ maximalIdeal R := Ideal.mul_mem_right _ _ hru
    have h2 : r * y - 1 ∈ maximalIdeal R :=
      hpm (Ideal.Quotient.eq_zero_iff_mem.1 (by rw [map_sub, map_mul, hb, map_one, sub_self]))
    have h3 := (maximalIdeal R).sub_mem h1 h2
    rw [sub_sub_cancel] at h3
    exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 h3)
  have hA : ¬ IsField (R ⧸ p) := by
    intro hF
    have h0 : Ideal.Quotient.mk p r₀ ≠ 0 := fun h => hr₀p (Ideal.Quotient.eq_zero_iff_mem.1 h)
    obtain ⟨b, hb⟩ := hF.mul_inv_cancel h0
    exact hr₀ (hunit r₀ (Units.mkOfMulEqOne _ b hb).isUnit)
  let k₀ := FractionRing (R ⧸ p)
  let φ₀ : R →+* k₀ := (algebraMap (R ⧸ p) k₀).comp (Ideal.Quotient.mk p)
  let σ : k₀ →+* AlgebraicClosure k₀ := algebraMap k₀ (AlgebraicClosure k₀)
  let G₀ := (Over.pullback (spMap φ₀)).obj G
  have hG₀ : IsSemiAbelian G₀ := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm
      infer_instance
    · have := hG.smooth
      change Smooth (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · have := hG.separated
      change IsSeparated (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · have := hG.quasiCompact
      change QuasiCompact (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · have := hG.geomConnected
      change GeometricallyConnected (pullback.snd G.hom (spMap φ₀))
      infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ spMap φ₀)
      exact ⟨torusExtOfIso (pullCompIso q (spMap φ₀) G) E⟩
  haveI := hG₀.smooth
  haveI := hG₀.quasiCompact
  haveI := hG₀.separated
  have T₀ : Nonempty (TorusExtension ((Over.pullback (spMap σ)).obj G₀)) :=
    torusExtension_iterate _ _ G (by rw [← spMap_comp']; exact hG.fibres _ _)
  obtain ⟨T⟩ := T₀
  obtain ⟨s, hs, H⟩ := FieldModel.exists_finite_torusExtension_range σ G₀ T
  haveI : Finite s := hs.to_subtype
  let k' := IntermediateField.adjoin k₀ s
  haveI : FiniteDimensional k₀ k' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  letI : Algebra (R ⧸ p) k' := ((algebraMap k₀ k').comp (algebraMap (R ⧸ p) k₀)).toAlgebra
  haveI : IsScalarTower (R ⧸ p) k₀ k' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  obtain ⟨V, hV, hdom⟩ := (discreteValuationRing_dominating_noetherian_local (R := R ⧸ p) (K := k₀) k').1 hA
  rw [LocalSubring.le_def] at hdom
  obtain ⟨hsub, hloc⟩ := hdom
  have hmem : ∀ a : R ⧸ p, algebraMap (R ⧸ p) k' a ∈ V := fun a => hsub ⟨a, rfl⟩
  have hinjA : Function.Injective (algebraMap (R ⧸ p) k') :=
    (algebraMap k₀ k').injective.comp (IsFractionRing.injective (R ⧸ p) k₀)
  let ψA : (R ⧸ p) →+* V := (algebraMap (R ⧸ p) k').codRestrict V hmem
  let ψ : R →+* V := ψA.comp (Ideal.Quotient.mk p)
  have hψ : IsLocalHom ψ := by
    refine ⟨fun r hr => hunit r ?_⟩
    set a := Ideal.Quotient.mk p r
    have h1 : IsUnit (Subring.inclusion hsub ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩) := hr
    obtain ⟨⟨u, v, huv, _⟩, hu⟩ := hloc.map_nonunit _ h1
    have hu' : u = ⟨algebraMap (R ⧸ p) k' a, a, rfl⟩ := hu
    subst hu'
    obtain ⟨b, hb⟩ := v.2
    refine (Units.mkOfMulEqOne a b (hinjA ?_)).isUnit
    have := congrArg Subtype.val huv
    rw [map_mul, map_one, hb]
    exact this
  let κ := ResidueField W
  let gA : (R ⧸ p) →+* κ := Ideal.Quotient.lift p ((residue W).comp g) (fun a ha => by
    show residue W (g a) = 0
    exact (residue_eq_zero_iff _).2 (Ideal.mem_comap.1 ha))
  have hgA : Function.Injective gA := by
    refine (injective_iff_map_eq_zero _).2 fun a ha => ?_
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective a
    have ha' : residue W (g r) = 0 := ha
    have : g r ∈ maximalIdeal W := (residue_eq_zero_iff _).1 ha'
    exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_comap.2 this)
  let g₀ : k₀ →+* κ := IsFractionRing.lift hgA
  let e : k' ≃ₐ[V] FractionRing V := IsLocalization.algEquiv (nonZeroDivisors V) k' (FractionRing V)
  let α₀ : k₀ →+* FractionRing V := e.toRingEquiv.toRingHom.comp (algebraMap k₀ k')
  let β₀ : FractionRing V →+* AlgebraicClosure k₀ := (algebraMap k' (AlgebraicClosure k₀)).comp e.symm.toRingEquiv.toRingHom
  have hβα : β₀.comp α₀ = σ := by
    ext x
    simp [α₀, β₀, σ]
  have hsr : s ⊆ Set.range β₀ := fun x hx =>
    ⟨e ⟨x, IntermediateField.subset_adjoin k₀ s hx⟩, by simp [β₀]⟩
  have T₂ := torusExtension_compose _ _ G (H (FractionRing V) α₀ β₀ hβα hsr)
  have key : α₀.comp φ₀ = (algebraMap V (FractionRing V)).comp ψ := by
    ext r
    show e (algebraMap k₀ k' (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) =
      algebraMap V (FractionRing V) (ψA (Ideal.Quotient.mk p r))
    rw [← e.commutes]
    rfl
  obtain ⟨L, _, i, j, hij⟩ := exists_common_ext α₀ g₀
  refine ⟨V, inferInstance, inferInstance, hV, ψ, L, inferInstance, i, j.comp (residue W), hψ, ?_, ?_, ?_⟩
  · intro x hx
    simp [(residue_eq_zero_iff x).2 hx]
  · rw [RingHom.comp_assoc, ← key]
    ext r
    have h1 := congrArg (fun f => f (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) hij
    simp only [RingHom.coe_comp, Function.comp_apply] at h1 ⊢
    show i (α₀ (algebraMap (R ⧸ p) k₀ (Ideal.Quotient.mk p r))) = _
    rw [h1]
    simp [g₀, gA, φ₀, IsFractionRing.lift_algebraMap]
  · rw [← key, spMap_comp']
    exact T₂
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteGroupCharactersOnLiftFormsExtendedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

noncomputable section

namespace GlobalTheory.Mem.R3.ChiExt

theorem res_unique {E : Type} [Field E] [NumberField E] {χ : Formalism.L2.Host.HChar E} {P : Pl E} {c c' : (kP P)ˣ →* ℂˣ}
    (h : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c u = χ.locK P k)
    (h' : ∀ (a : 𝓞 E) (k : Eˣ) (u : (kP P)ˣ), (k : E) = a → (u : kP P) = Ideal.Quotient.mk _ a → c' u = χ.locK P k) : c = c' := by
  ext1 u
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (u : kP P)
  have ha0 : (a : E) ≠ 0 := by
    intro h0
    have : a = 0 := by exact_mod_cast h0
    exact u.ne_zero (by rw [← ha, this, map_zero])
  exact (h a (Units.mk0 _ ha0) u rfl ha.symm).trans (h' a (Units.mk0 _ ha0) u rfl ha.symm).symm

theorem prod_eq {B B' : Base} (hB : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} (hf : HEq f' f)
    {px : PreX B.toPre} {px' : PreX B'.toPre} (hpx : HEq px' px) (j : Fin B.R.m) (j' : Fin B'.R.m) (hj : (j : ℕ) = j')
    {Pg : Finset (Pl B.host.E)} {Pg' : Finset (Pl B'.host.E)} (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* G0 Pg B.R.r) (eG' : Gc B' px' ≃* G0 Pg' B'.R.r) (heG : HEq eG' eG)
    (c : ∀ PP : Pl B.host.E, (kP PP)ˣ →* ℂˣ) (c' : ∀ PP : Pl B'.host.E, (kP PP)ˣ →* ℂˣ)
    (h : ∀ PP ∈ Pg, ∀ (a : 𝓞 B.host.E) (k : B.host.Eˣ) (u : (kP PP)ˣ), (k : B.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c PP)⁻¹ u = (f.mu0 j).locK PP k)
    (h' : ∀ PP ∈ Pg', ∀ (a : 𝓞 B'.host.E) (k : B'.host.Eˣ) (u : (kP PP)ˣ), (k : B'.host.E) = a → (u : kP PP) = Ideal.Quotient.mk _ a →
      (c' PP)⁻¹ u = (f'.mu0 j').locK PP k)
    (g : Gc B px) (g' : Gc B' px') (hg : HEq g' g) :
    ∏ PP : Pg', ((c' PP.1 (Matrix.GeneralLinearGroup.det (eG' g' PP)) : ℂˣ) : ℂ) =
      ∏ PP : Pg, ((c PP.1 (Matrix.GeneralLinearGroup.det (eG g PP)) : ℂˣ) : ℂ) := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  obtain rfl : px' = px := eq_of_heq hpx
  obtain rfl : f' = f := eq_of_heq hf
  obtain rfl : Pg' = Pg := eq_of_heq hPg
  obtain rfl : eG' = eG := eq_of_heq heG
  obtain rfl : g' = g := eq_of_heq hg
  obtain rfl : j = j' := Fin.ext hj
  refine Finset.prod_congr rfl fun PP _ => ?_
  have e : c' PP.1 = c PP.1 := inv_injective (res_unique (h' PP.1 PP.2) (h PP.1 PP.2))
  rw [e]
  rfl


set_option maxHeartbeats 2000000 in
theorem chi_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∀ (g : Gc (w.st Z).B w.px) (g' : Gc (w'.st Z').B w'.px), HEq g' g → (((z'.R.toRealDat.FW j').chi g' : (w'.st Z').toD7.what₂.LLˣ) : (w'.st Z').toD7.what₂.LL) = φ (((z.R.toRealDat.FW j).chi g : (w.st Z).toD7.what₂.LLˣ) : (w.st Z).toD7.what₂.LL)) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE hf _ hpx Z hX Wt z _ _ _ _ Z' hX' _ _ _ z' _ hx j j' hj φ hφ g g' hg => ?_
  apply RingHom.injective (w'.st Z').toD7.what₂.embLL
  refine (z'.pins.char.base.grp.chiW j' g').trans (Eq.trans ?_ ((hφ _).trans (z.pins.char.base.grp.chiW j g)).symm)
  have hC : z.R.toLevCh.C.mu0 j = f.mu0 j := by
    rw [z.lev.C, w.C_eq]; rfl
  have hC' : z'.R.toLevCh.C.mu0 j' = f'.mu0 j' := by
    rw [z'.lev.C, w'.C_eq]; rfl
  exact prod_eq hE.1 hf hpx j j' hj hx.Pg z.R.eG z'.R.eG hx.eG (z.R.chi ((j : ℕ) + 1)) (z'.R.chi ((j' : ℕ) + 1))
    (fun PP hP => hC ▸ z.lev.is.chi j PP hP) (fun PP hP => hC' ▸ z'.lev.is.chi j' PP hP) g g' hg

end GlobalTheory.Mem.R3.ChiExt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedTupleReadingLevelCharacterStatement
section
open scoped TensorProduct
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TypeLev Matrix Formalism.L2.Forms GlobalTheory.SeeSaw.TwLev
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedTuple_reading_level_character : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l))
    (a : I.ι) {bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))}
    (S : StepLevel (I.rec7 l Z).host.F (I.rec7 l Z).host.E (sigD (I.rec7 l Z)) (gramP (I.rec7 l Z)) 1 (I.rec7 l Z).R.f bad)
    {y lat st}, I.ReadsP a S.Lb S.U S.chi y lat st → ∀ (_c : (I.stX a).Cl) (ξ : ∀ PP : Pl (I.rec7 l Z).host.E, (kP PP)ˣ →* ℂˣ),
    (∀ PP ∈ I.Q a, ∀ x, ((ξ PP x : ℂˣ) : ℂ) =
      B.embLL ((Formalism.L2.DIV.resChar (I.tup a : Formalism.L2.DIV.Chr B.fields.F B.fields.E B.fields.K) PP x : B.LLˣ) : B.LL)) →
    RdLevOn (E := B.fields.E) B.sp.cm (RatAt (I.Q a)) S.U S.chi (rowTyG I.Ch I.Ps) B.embLL (I.Q a)
      (fun _ => blockTri (blk2 B.R.r)) (fun P => (ξ P.1).comp (blkDet (blk2 B.R.r) 1)) := by
  first | exact @GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | exact GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw | (intros; apply GlobalTheory.SeeSaw.TwLev.rdLevOn_reads_tw <;> assumption)
end

