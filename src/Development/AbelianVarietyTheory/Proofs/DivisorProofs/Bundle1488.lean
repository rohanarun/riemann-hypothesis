module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1073
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1448
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiabelianGenericFibrePolarizationIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU GlobalTheory.LN GlobalTheory.PsiRing

noncomputable section
namespace GlobalTheory.SectionUnif

theorem exists_shift {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R) {q : R} (hq : q ≠ 0) :
    ∃ c : ℕ, ∀ (n : ℕ) (a : R), q * a ∈ I ^ (n + c) → a ∈ I ^ n := by
  first
  | exact @_root_.GlobalTheory.ClosingLemmaSecond.main
  | exact _root_.GlobalTheory.ClosingLemmaSecond.main
  | (apply _root_.GlobalTheory.ClosingLemmaSecond.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ClosingLemmaSecond.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ClosingLemmaSecond.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ClosingLemmaSecond.main ..)

section
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
  [IsCommMonObj G']

theorem exists_term_ne_zero [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (U : PreU I D A G) (k : ℕ)
    (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α) (hf : U.ExpT (𝟙_ _) k σ f) (y : (𝟙_ _ ⊗ G).left)
    (hy : y ∈ nonzeroLocus σ) : ∃ α j, (f α).f j ≠ 0 := by
  by_contra h0
  push Not at h0
  have := U.semi.smooth
  have := U.semi.geomConnected
  have hL := U.P.L.isLB
  have lam : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
    rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
  obtain ⟨s, hs⟩ := BaseExpansionExists.exists_pull (λ_ G).inv.left (fun _ => rfl) σ
  have h₀ := (sec_eq_zero_and_hom_eq_of_thickenings R I hI G).1 _ (DVR.linComb_isLB _ hL _ _) s
    fun e j => fn_ext fun z hz => by
      have hz' : (𝟙 (thickObj R I e G).left : _ ⟶ _) z ∈ (fstG I e G).left ⁻¹ᵁ _ := hz
      refine (gs_pull (𝟙 _) (fstG I e G).left z _ hz' _).trans (Eq.trans ?_ ((gs_eq (𝟙 _) z _ hz' _).trans
        ((congrArg _ (map_zero _)).trans (map_zero _))).symm)
      refine ExpUniq.gs_eq_zero_of_sval hL s _ z (fun JG hJG => (hs _ _ z JG hJG).trans ?_) j hz'
      let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I e)).obj (thickObj R I e G)
      let b : T ⟶ D.P.A := (U.gt e).pG
      let x : T ⟶ G := fstG I e G
      have hG : (lift (toUnit T) x).left ≫ (snd _ G).left = x.left := by rw [← Over.comp_left, lift_snd]
      have hB : (lift (toUnit T) b).left ≫ (snd _ D.P.A).left = b.left := by rw [← Over.comp_left, lift_snd]
      have hF : (lift (toUnit T) b).left ≫ (fst _ D.P.A).left = (lift (toUnit T) x).left ≫ (fst _ G).left := by
        rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
      have hi : lift (toUnit T) x = x ≫ (λ_ G).inv := by ext1 <;> simp [toUnit_unique]
      have hi' : (lift (toUnit T) x).left = (𝟙 _ ≫ (fstG I e G).left) ≫ (λ_ G).inv.left := by
        rw [hi, Category.id_comp]; rfl
      obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
      obtain ⟨t, ht⟩ := hf e
      obtain ⟨-, hsum⟩ := ht T.left (𝟙 _) _ _ (hG.trans (Category.id_comp _).symm)
        (hB.trans (Category.id_comp _).symm) hF z JG J hJG hJ
      rw [Finset.sum_eq_zero fun α _ => by
        rw [ThetaScalar.sval_eq_zero _ (h0 α) _ z hJ, MulZeroClass.zero_mul]] at hsum
      rw [← hi']
      exact (((Units.isUnit _).pow k).mul_right_eq_zero).1 hsum
  obtain ⟨J, hJ⟩ := exists_good_pt hL y
  have E := (hs _ (snd (𝟙_ _) G).left y J hJ).symm.trans (ThetaScalar.sval_eq_zero _ h₀ _ y hJ)
  rw [lam] at E
  have u := (MulPullSec.mem_nonzeroLocus_iff σ (𝟙 _) y hJ).1 hy
  rw [E] at u
  exact not_isUnit_zero u

theorem exists_sec_point (U : PreU I D A G) (θ : LB.Sec U.P.L.L) (k : U.P.L.L.ι) (hθ : θ.f k ≠ 0) :
    ∃ (σ : U.SecGT (𝟙_ _) 1) (y : (𝟙_ _ ⊗ G).left), y ∈ nonzeroLocus σ := by
  have := U.semi.smooth
  have : IsReduced G.left := isReduced_of_smooth_of_isReduced G.hom
  have := FibreNonzero.isIso_snd_left G
  have h : G.left.basicOpen (θ.f k) ≠ ⊥ := fun h => hθ ((basicOpen_eq_bot_iff _).1 h)
  obtain ⟨g, hg⟩ := (TopologicalSpace.Opens.ne_bot_iff_nonempty _).1 h
  obtain ⟨z, rfl⟩ := (snd (𝟙_ _) G).left.surjective g
  exact ⟨FibreNonzero.pullOne θ _, z, FibreNonzero.mem_nonzeroLocus_pullOne θ _ z k hg⟩

theorem exists_point_of_cmp {φ : R →+* V} (hφ : Function.Injective φ) {U : PreU I D A G} {U' : PreU I' D' A' G'}
    {F : G'.left ⟶ G.left} (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (σ' : U'.SecGT (𝟙_ _) k)
    (h : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left),
      r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' →
      sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k *
        sval σ' r' z J') (y : (𝟙_ _ ⊗ G).left) (hy : y ∈ nonzeroLocus σ) : ∃ y', y' ∈ nonzeroLocus σ' := by
  have := U.semi.smooth
  have := FibreNonzero.isIso_snd_left G
  have := FibreNonzero.isIso_snd_left G'
  have : IsSchemeTheoreticallyDominant (spMap φ) := schDom_spec_map φ hφ
  have : IsSchemeTheoreticallyDominant F := .of_isPullback C.pb.1.flip
  have : QuasiCompact F := MorphismProperty.of_isPullback C.pb.1.flip inferInstance
  let r : (𝟙_ _ ⊗ G').left ⟶ (𝟙_ _ ⊗ G).left := (snd (𝟙_ _) G').left ≫ F ≫ inv (snd (𝟙_ _) G).left
  have hr : r ≫ (snd _ G).left = 𝟙 _ ≫ (snd _ G').left ≫ F := by simp [r]
  have : IsDominant r := by unfold r; infer_instance
  obtain ⟨z', hz'⟩ := r.denseRange.exists_mem_open (nonzeroLocus σ).isOpen ⟨y, hy⟩
  obtain ⟨J, hJ⟩ := exists_good_pt U.P.L.isLB z'
  obtain ⟨J', hJ'⟩ := exists_good_pt U'.P.L.isLB z'
  have u := (MulPullSec.mem_nonzeroLocus_iff σ r z' hJ).1 hz'
  rw [h _ (𝟙 _) r hr z' J J' hJ hJ'] at u
  exact ⟨z', (MulPullSec.mem_nonzeroLocus_iff σ' (𝟙 _) z' hJ').2 (isUnit_of_mul_isUnit_right u)⟩

end

theorem ne_zero_and_psiCmp (h₁ : Laws) (h₂ : Laws2) {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]
    [IsLocalRing V] {I : Ideal R} (hV : CDvr V) {φ : R →+* V} (hφ : Function.Injective φ) {D : DegPre R}
    {D' : DegData V (IsLocalRing.maximalIdeal V)} {A : PolAV (Sp (FractionRing R))} {A' : PolAV (Sp (FractionRing V))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G']
    [IsCommMonObj G'] {U : PreU I D A G} {U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G'}
    {U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G'} {F : G'.left ⟶ G.left} (C : Cmp φ U U' F)
    (hU : Under U' U₀.toUnifPre) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (hf : U.ExpT (𝟙_ _) 1 σ f)
    (y : (𝟙_ _ ⊗ G).left) (hy : y ∈ nonzeroLocus σ) :
    (∀ α, ∃ j, (f α).f j ≠ 0) ∧ ∀ psi h, PsiRel (withPsi D psi h) (𝟙_ _) f →
      RigCmp φ (withPsi D psi h) D'.toPre C.β C.v ∧ ∃ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ ∧
        PsiCmp (withPsi D psi h) D'.toPre C.β C.v C.xe gam := by
  have := hV.1
  have hV' : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : IsLocalRing.maximalIdeal V ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  obtain ⟨σ', f', hf', hσσ, hff⟩ := ExpCmp.expT_cmp R V I _ φ C.map_le D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := _root_.GlobalTheory.PsiExpansion.psiRel_of_expT h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  obtain ⟨y', hy'⟩ := exists_point_of_cmp hφ C 1 σ σ' hσσ y hy
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 := _root_.GlobalTheory.forall_ne_zero_of_psiRel V D'.toPre f' hrel'
    (exists_term_ne_zero (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge U' 1 σ' f' hf' y' hy')
  refine ⟨ne_zero_of_secCmp C.pbB.1.w hcmp hne', fun psi h hrel => ?_⟩
  have hrig : RigCmp φ (withPsi D psi h) D'.toPre C.β C.v :=
    _root_.GlobalTheory.rigCmp_of_cmp R V I _ φ hm C.map_le D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := exists_generic_map hφ
  exact ⟨hrig, gam, hgam, _root_.GlobalTheory.psiCmp_of_secCmp R V φ (withPsi D psi h) D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp
    hrel hrel' (hne' 0) gam hgam⟩


set_option maxHeartbeats 1600000 in
theorem exists_cmp {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} (hR : AdmBase R I)
    {D : DegPre R} {A : PolAV (Sp (FractionRing R))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : PreU I D A G) (hW : HypW G U.P.L.L) (hsp : SplitOver G I)
    (hA : LBIso (A.L.pull U.gen.hom.left) (U.P.L.L.pull (pullback.fst G.hom (jK R))))
    (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (φ : R →+* V) (hV : CDvr V) (hφ : Function.Injective φ)
    (hc : (IsLocalRing.maximalIdeal V).comap φ = I) :
    ∃ (D' : DegData V (IsLocalRing.maximalIdeal V)) (A' : PolAV (Sp (FractionRing V)))
      (G' : Over (Spec (CommRingCat.of V))) (_ : GrpObj G') (_ : IsCommMonObj G') (F : G'.left ⟶ G.left)
      (U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G') (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G'),
      Under U' U₀.toUnifPre ∧ Nonempty (Cmp φ U U' F) := by
  obtain ⟨hL, hL2, hL3, -⟩ := GlobalTheory.allSixLaws
  have := hV.1
  have := U.gen_hom
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hle : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hc.ge
  obtain ⟨A', s, w, hw⟩ := PrimeUnif.exists_setting hL hL2 hL3 U.P U.semi hW hsp A U.gen hA hV φ hφ hc.ge
  obtain ⟨D', U₀, hLG, -, -⟩ := GlobalTheory.uniformisation_dvr_unconditional V A' _ s
  obtain ⟨U', hU'⟩ := (GlobalTheory.LN.PreForm.under_exists_and_expands hL hL2 V _ D' A' _ s.semi).1 U₀.toUnifPre
  have := s.semi.smooth
  obtain ⟨w', hw'⟩ := PrimeUnif.isCPMap_of_eq hL.globalFns s.gen s.P U'.P (hU'.2.1.trans hLG) hw
  obtain ⟨C, -⟩ := _root_.GlobalTheory.LN.PreCompare.exists_cmp hL hL2 ega_holds R V I _ hR hB (IsLocalRing.maximalIdeal.isMaximal V).ne_top φ hle D _ A A'
    G _ U U' _ (isGrpPullback_pullback G _) w' hw'
  exact ⟨D', A', _, _, _, _, U₀, U', hU', ⟨C⟩⟩


set_option maxHeartbeats 1600000 in
theorem exists_unif_of_ne_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.LN.admitted R (IsLocalRing.maximalIdeal R) → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (P : CP G), IsSemiAbelian G → HypW G P.L.L → GlobalTheory.LN.SplitOver G (IsLocalRing.maximalIdeal R) → ∀ (A : PolAV (Sp (FractionRing R))) (gen : (Over.pullback (jK R)).obj G ≅ A.A), IsMonHom gen.hom → LBIso (A.L.pull gen.hom.left) (P.L.L.pull (pullback.fst G.hom (jK R))) → (∃ (σ : LB.Sec P.L.L) (k : P.L.L.ι), σ.f k ≠ 0) → ∃ (D : DegData R (IsLocalRing.maximalIdeal R)) (U : Unif (IsLocalRing.maximalIdeal R) D A G), U.LG = P.L ∧ U.gen = gen := by
  intro R _ _ _ hR G _ _ P hS hW hsp A gen hgen hA ⟨θ, k, hθ⟩
  obtain ⟨h₁, h₂, h₃, -⟩ := GlobalTheory.allSixLaws
  have := hR.1.1
  have := hR.1.2.2.1
  have := hR.2.2.1
  have hI : IsLocalRing.maximalIdeal R ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hpi : IsPrincipalIdealRing (R ⧸ IsLocalRing.maximalIdeal R) := by
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal R)
    infer_instance
  obtain ⟨D, U, rfl, rfl⟩ := _root_.GlobalTheory.PreUnifLocal.exists_preU_local h₁ h₂ h₃ ega_holds GlobalTheory.uniformisation_dvr_unconditional R _ hR hpi G P hS hW hsp
    A gen hgen hA
  obtain ⟨σ, y, hy⟩ := exists_sec_point U θ k hθ
  obtain ⟨f, hf, -⟩ := CompleteBaseExpansion.main h₁ h₂ ega_holds R _ hR.1 hI D A G U 1 σ
  obtain ⟨V, _, _, _, φ, hV, hφ, hc⟩ := PrimeUnif.exists_cdvr R (IsLocalRing.maximalIdeal R)
  obtain ⟨D', A', G', _, _, F, U₀, U', hU', ⟨C⟩⟩ := exists_cmp hR.1 U hW hsp hA V φ hV hφ hc
  obtain ⟨hne, hps⟩ := ne_zero_and_psiCmp h₁ h₂ hV hφ C hU' σ f hf y hy
  obtain ⟨psi, h, hrel⟩ := exists_psi_psiRel h₁ h₂ R D f hne
  let E : DegPre R := withPsi D psi h
  have hrelE : PsiRel E (𝟙_ _) f := hrel
  obtain ⟨hrig, gam, hgam, hpsi⟩ := hps psi h hrel
  have hev : E.PsiEven :=
    _root_.GlobalTheory.PsiRing.psiEven_descend h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    _root_.GlobalTheory.tauBimult_of_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨hD, hD₁, hD₂, hD₃⟩ :=
    _root_.GlobalTheory.PsiRing.exists_isPullDeg_of_cmp R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi hbi
  obtain ⟨ga, a, hSc⟩ := exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := _root_.GlobalTheory.PsiRing.exists_basis_fibNZ h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hSc χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hSc hrelE hth χ q (b χ) hq (hb χ)
  have hq0 : q ≠ 0 := by
    rintro rfl
    obtain ⟨j, hj⟩ := hne 0
    refine hj (ThetaScalar.eq_zero_of_sval D.P.isLB _ (fun z J hJ => ?_) j)
    rw [hq _ _ z J hJ, Geo.Tor.cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero, map_zero, MulZeroClass.zero_mul]
  have hW' : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (g : R →+* W), CDvr W → Function.Injective g →
      (IsLocalRing.maximalIdeal W).comap g = IsLocalRing.maximalIdeal R → ∀ χ : D.X, χ ≠ 0 →
      ∃ m ∈ IsLocalRing.maximalIdeal W, g (b χ) = g q * m := fun W _ _ _ g hW₁ hg hgc χ hχ => by
    obtain ⟨D₁, A₁, G₁, _, _, F₁, U₁, U₂, hU₁, ⟨C₁⟩⟩ := exists_cmp hR.1 U hW hsp hA W g hW₁ hg hgc
    obtain ⟨-, gam₁, hgam₁, hpsi₁⟩ := (ne_zero_and_psiCmp h₁ h₂ hW₁ hg C₁ hU₁ σ f hf y hy).2 psi h hrel
    obtain ⟨x, rfl⟩ := C₁.xe.surjective χ
    exact GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R W g E D₁.toPre C₁.β C₁.v C₁.xe C₁.pbB C₁.v_gen C₁.c_pr gam₁ hgam₁ hpsi₁ ga a hSc x _
      (D₁.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
  have hdiv : ∀ χ : D.X, χ ≠ 0 → ∃ r ∈ IsLocalRing.maximalIdeal R, b χ = q * r := fun χ hχ => by
    obtain ⟨r, hr⟩ := ValCrit.dvd_of_forall_cdvr R (b χ) q hq0 fun W _ _ _ g hW₁ hg hgc =>
      (hW' W g hW₁ hg hgc χ hχ).elim fun m hm => ⟨m, hm.2⟩
    obtain ⟨m, hm₁, hm₂⟩ := hW' V φ hV hφ hc χ hχ
    rw [hr, map_mul] at hm₂
    refine ⟨r, hc.le (Ideal.mem_comap.2 ?_), hr⟩
    rwa [mul_left_cancel₀ ((map_ne_zero_iff φ hφ).2 hq0) hm₂]
  have hin : ∀ (χ : D.X) (J : Ideal R) (r : R), r ∈ J → b χ = q * r → E.PsiIn χ J := fun χ J r hJ e =>
    (PsiScalIn.main_local E ga a hSc χ J).2 ⟨r, hJ, mul_left_cancel₀
      ((map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hq0) (((map_mul _ q r).symm.trans (congrArg _ e.symm)).trans (hab χ).symm)⟩
  obtain ⟨c, hcs⟩ := exists_shift (IsLocalRing.maximalIdeal R) hq0
  let Dd : DegData R (IsLocalRing.maximalIdeal R) :=
    ⟨E, hev, hbi, fun χ hχ => (hdiv χ hχ).elim fun r hr => hin χ _ r hr.1 hr.2, fun n => by
      classical
      obtain ⟨s, hs⟩ := GlobalTheory.T.expansionCoef_mem_adic_pow R _ hI D A G U σ f th hf hth (n + c)
      refine (insert 0 s).finite_toSet.subset fun χ hχ => ?_
      by_contra hn
      rw [Finset.mem_coe, Finset.mem_insert, not_or] at hn
      obtain ⟨r, -, hr⟩ := hdiv χ hn.1
      exact hχ (hin χ _ r (hcs n r (hr ▸ Ideal.pow_le_pow_right (Nat.le_succ _) (hs χ hn.2 _ _ (hb χ)))) hr)⟩
  have := hV.1
  have hB : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  obtain ⟨U₂, C₂, hD₄, eP, eg, k₁, k₂, k₃⟩ := PrimeUnif.exists_move psi h C hD Dd.toPre rfl hD₁ hD₂ hD₃
  obtain ⟨U₁, -, hU₁, -⟩ := GlobalTheory.UnifDescent.exists_unif_of_cmp h₁ h₂ ega_holds R V _ _ hR.1 hB hI φ hφ C.map_le Dd D' A A'
    G _ U₂ U' U₀ _ C₂ hD₄ hU' k₁ k₂ k₃
  exact ⟨Dd, U₁, hU₁.2.1.symm.trans (congrArg CP.L eP), hU₁.1.symm.trans eg⟩

end GlobalTheory.SectionUnif
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentConstantPathEqZero
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

namespace GlobalTheory.Nef

theorem tan_triv_eq_zero : ∀ (k K E : Type) [Field k] [IsAlgClosed k] [CharZero k] [Field K] [Algebra k K] [Field E] [Algebra k E] [Algebra K E] [IsScalarTower k K E] [FiniteDimensional K E] (C : Scheme.{0}) [Algebra k Γ(C, ⊤)] (x : Sp K ⟶ C), IsGenOver k x →
  ∀ (G : Over C) [GrpObj G], IsSemiAbelian G → ∀ (W : C.Modules) (r : ℕ) (i : W ⟶ Lie G), Mono i → ∀ (V₀ : C.Opens) (s : Fin r → Γ(W, V₀)), (V₀ : Set C).Nonempty → IsFrame s → ∀ w : Fin r → E, HasTan G (spMap (algebraMap K E) ≫ x) (triv G (spMap (algebraMap K E) ≫ x)) (fun j => i.app V₀ (s j)) w → w = 0 := by
  intro k K E _ _ _ _ _ _ _ _ _ _ C _ x hx G _ hG W r i hi V₀ s hV₀ hs w hw
  haveI := hG
  haveI := hi
  haveI : IsIntegral C := LieSemineg.isIntegral_curve hx.1.1 hx.1.2.2
  haveI : Smooth G.hom := hG.smooth
  obtain ⟨h₀, -, -⟩ := _root_.GlobalTheory.Nef.isGen_evAt_frac K C x hx.2.1 V₀ hV₀
  have hp₀ : x (IsLocalRing.closedPoint K) ∈ V₀ := (_root_.GlobalTheory.Nef.evAt_calculus.2.2.2.1 K C x V₀).1 h₀
  obtain ⟨U₁, n, om, hpU₁, hom⟩ := exists_isFrame_omega G (x (IsLocalRing.closedPoint K))
  obtain ⟨V', U, hpV', hV'le, c⟩ := GlobalTheory.Conormal.exists_isChart (he := sec_hom η[G])
    (show x (IsLocalRing.closedPoint K) ∈ V₀ ⊓ U₁ from ⟨hp₀, hpU₁⟩)
  have hV : V' ≤ V₀ := hV'le.trans inf_le_left
  have hVU : V' ≤ U₁ := hV'le.trans inf_le_right
  obtain ⟨hx', hinj, -⟩ := _root_.GlobalTheory.Nef.isGen_evAt_frac K C x hx.2.1 V' ⟨_, hpV'⟩
  have hb : ⊤ ≤ (spMap (algebraMap K E) ≫ x) ⁻¹ᵁ V' := fun z _ => hx' (Set.mem_univ _)
  have hev : ∀ g : Γ(C, V'), evAt (spMap (algebraMap K E) ≫ x) hb g = algebraMap K E (evAt x hx' g) :=
    fun g => _root_.GlobalTheory.Nef.evAt_calculus.1 K E C (algebraMap K E) x V' hx' hb g
  have key : ∀ f : Γ(G.left, U), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV (dUnit G c.le f))) = 0 := by
    intro f
    have h2 : ⊤ ≤ ((spMap (algebraMap K E) ≫ x) ≫ unitSec G) ⁻¹ᵁ U := fun z _ => c.le (hb (Set.mem_univ z))
    have hU : ⊤ ≤ (triv G (spMap (algebraMap K E) ≫ x)) ⁻¹ᵁ U := fun z _ => h2 (Set.mem_univ _)
    have := hw U hU V' hV c.le hb f
    simp only [hev] at this
    rw [← this]
    have e1 : evAt (triv G (spMap (algebraMap K E) ≫ x)) hU f = PowerSeries.C (R := E) (evAt _ h2 f) :=
      _root_.GlobalTheory.Nef.evAt_calculus.1 E (PowerSeries E) G.left (PowerSeries.C (R := E)) _ U h2 hU f
    rw [e1]
    simp
  have key2 : ∀ e' : Γ(omega G, V'), ∑ j, w j * algebraMap K E (evAt x hx'
      (dualApp (i.app V₀ (s j)) hV e')) = 0 := by
    intro e'
    obtain ⟨f, rfl⟩ := c.d_surjective (sec_hom η[G]) e'
    exact key f
  haveI : Nonempty V' := ⟨⟨_, hpV'⟩⟩
  let N : Matrix (Fin r) (Fin n) Γ(C, V') := fun j a => dualApp (i.app V₀ (s j)) hV (resM (omega G) hVU (om a))
  have hN : LinearIndependent Γ(C, V') N.row := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hl : (∑ j, g j • resM (Lie G) hV (i.app V₀ (s j))) = 0 := by
      refine hom.dual_ext hVU (fun a => ?_)
      have := congrFun hg a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, Matrix.row, N] at this
      rw [dualApp_sum, LinearMap.sum_apply, dualApp_zero, LinearMap.zero_apply]
      simpa only [dualApp_smul, LinearMap.smul_apply, smul_eq_mul, dualApp_res, GlobalTheory.LB.resG_self] using this
    have hs' : ∑ j, g j • resM W hV (s j) = 0 := by
      apply QCoh.injective_app_of_mono i V'
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_zero, Scheme.Modules.Hom.app_smul, Twist.app_resM]
      exact hl
    have hli := (hs.basis hV).linearIndependent
    rw [hs.coe_basis hV, Fintype.linearIndependent_iff] at hli
    exact hli g hs'
  obtain ⟨σ, hσ⟩ := LieSemineg.exists_det_ne_zero N hN
  let φ : Γ(C, V') →+* E := (algebraMap K E).comp (evAt x hx')
  have hφ : Function.Injective φ := (algebraMap K E).injective.comp hinj
  have hA : ((N.submatrix id σ).map φ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact fun h => hσ (hφ (h.trans (map_zero φ).symm))
  refine Matrix.eq_zero_of_vecMul_eq_zero hA ?_
  funext a
  simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, Matrix.submatrix_apply, id, Pi.zero_apply, N, φ,
    RingHom.comp_apply]
  exact key2 _

end GlobalTheory.Nef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTorusLeLieSpan
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ChTor GlobalTheory.HTLat GlobalTheory.KernelNoTorsion GlobalTheory.HodgeTateTest GlobalTheory.PDiv GlobalTheory.SplitTorusPow
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorusTateLie

section Torus

variable (C : Type) [Field C] {O : Type} [CommRing O] [Algebra O C] {X : Type} [AddCommGroup X]

def evalChar (χ : X) : (specO O O ⟶ splitTorus (Sp O) X) →* Cˣ :=
  (Units.map ((algebraMap O C).comp (Scheme.ΓSpecIso (CommRingCat.of O)).hom.hom).toMonoidHom).comp
    ((MonoidHom.eval (Multiplicative.ofAdd χ)).comp
      (splitTorusPointsEquiv (Sp O) X (specO O O)).toMonoidHom)

def lieMap {G G' : Over (Sp O)} [GrpObj G] [GrpObj G'] (φ : G ⟶ G') [IsMonHom φ] (x : LieG G) : LieG G' :=
  ⟨x.1 ≫ φ, by rw [← Category.assoc, x.2, Category.assoc, IsMonHom.one_hom]⟩

variable {C} {p : ℕ} [Fact p.Prime]

end Torus

section AtPoint

variable {p : ℕ} [Fact p.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0}
  {O : Type} [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]
  {Λ : Type} [CommRing Λ] [StarRing Λ] (P : Point p v O Λ) (φ : GmO O ⟶ P.Gt) [IsMonHom φ]
  (ζ : Tate p (specO O O ⟶ GmO O)) (hζ : Tate.map p (evalChar C (ULift.up (1 : ℤ))) ζ = P.eps.1)

include hζ

variable [Algebra ℤ_[p] O]

variable [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

end AtPoint

end GlobalTheory.TorusTateLie
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformRationalTranslateQuasiInvariantCm
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaQuasiRatF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_cAF' (σ : E →ₐ[F] E) (z : AF F ⊗[F] E) : cA σ z = cAF σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => rfl
  | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]

theorem sum_three_fintype_reverse_order {ι κ μ M : Type} [Fintype ι] [Fintype κ] [Fintype μ] [AddCommMonoid M] (f : ι → κ → μ → M) :
    ∑ i, ∑ k, ∑ l, f i k l = ∑ l, ∑ k, ∑ i, f i k l := by
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl fun k _ => Finset.sum_comm]
  exact Finset.sum_comm

theorem symp_eq_symplOF' (σ : E →ₐ[F] E) {nS nT : ℕ} (JS : Matrix (Fin nS) (Fin nS) E)
    (JT : Matrix (Fin nT) (Fin nT) E) (ξ₀ : E) (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E)
    (ξ : AF F ⊗[F] E) (hA : JA = JTᵀ) (hB : ξ • incM F JB = incM F (ξ₀ • JS⁻¹)) (x y : WOF F E nS nT) :
    symp (cA σ) ξ (incM F JA) (incM F JB) x y = symplOF σ JS JT ξ₀ x y := by
  have hB' : ∀ j l, ξ * incM F JB j l = incAF F E ξ₀ * incAF F E (JS⁻¹ j l) := by
    intro j l
    have h1 := congrFun (congrFun hB j) l
    rw [Matrix.smul_apply, smul_eq_mul] at h1
    rw [h1]
    show inclR (F := F) (AF F) (ξ₀ * JS⁻¹ j l) = _
    exact map_mul _ _ _
  have hA' : ∀ i k, incM F JA i k = incAF F E (JT k i) := by
    intro i k; subst hA; rfl
  unfold symp hTens symplOF hOF
  congr 1
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_three_fintype_reverse_order]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
  rw [hA', cA_eq_cAF']
  calc ξ * (x i j * incAF F E (JT k i) * incM F JB j l * cAF σ (y k l))
      = x i j * incAF F E (JT k i) * (ξ * incM F JB j l) * cAF σ (y k l) := by ring
    _ = _ := by rw [hB']; ring

theorem thetaTr_ratWF_add : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
          (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
            co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
          ∀ Φ ∈ schA F κ, ∀ (γ : Matrix (Fin nT) (Fin nS) E) (w : WOF F E nS nT),
            GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ (ratWF γ + w) = B.ψ (-(symplOHF σ JS JT ξ₀ (ratWF γ) w)) * GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ w := by
  intro F E _ _ _ _ _ σ B _ hψ nS nT JS JT _ _ ξ₀ _ _ JA JB ξ hA hB κ _ co hrat Φ _ γ w
  obtain ⟨y, z, hyz⟩ := hrat γ
  have hγ : ratWF γ = incM F γ := rfl
  have hform := co.form (incM F γ) w
  rw [symp_eq_symplOF' σ JS JT ξ₀ JA JB ξ hA hB, hyz] at hform
  unfold GlobalTheory.WeilSchrodinger.thetaTr GlobalTheory.WeilM.Darboux.rho
  rw [map_add (f := _), hγ, hyz]
  set u : (κ → AF F) × (κ → AF F) :=
    (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) with hu
  set v := co.e w
  have law := GlobalTheory.ThetaQuasiRat.schr_schr B.ψ u v Φ
  have hinv : B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) *
      B.ψ (⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2)) = 1 := by
    rw [← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one]
  have hsum : GlobalTheory.WeilM.schr B.ψ (u + v) Φ =
      B.ψ (-(⅟(2 : AF F) * (u.1 ⬝ᵥ v.2 - v.1 ⬝ᵥ u.2))) • GlobalTheory.WeilM.schr B.ψ u (GlobalTheory.WeilM.schr B.ψ v Φ) := by
    rw [law, smul_smul, hinv, one_smul]
  have h2 : ⅟(2 : AF F) = algebraMap F (AF F) (1 / 2) := by
    apply invOf_eq_right_inv
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul]
    norm_num
  rw [hsum, GlobalTheory.ThetaQuasiRat.thetaSum_smul', hu, GlobalTheory.ThetaQuasiRat.thetaSum_schr_rat F B.ψ hψ.1.2.2.1 y z, ← hu,
    symplOHF, hform, h2]

end GlobalTheory.ThetaQuasiRatF
end
end

