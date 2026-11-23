module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2097
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2046
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2047
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PolOfSecondQuotient
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1144
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsBasisKaehlerOfAlgebraicIndependent
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanFinrankMaximalIdealLeNcardOfLeSupSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2029
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2119
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalOneCochainsBaseChangeBijectiveFiniteCategor
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private def piSL {R R' : Type} [CommRing R] [CommRing R'] {σ : R →+* R'} {J : Type} {M M' : J → Type}
    [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[σ] M' i) : (∀ i, M i) →ₛₗ[σ] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := by funext i; simp
  map_smul' r x := by funext i; simp [map_smulₛₗ]

private theorem piSL_bij {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} [Finite J]
    {M M' : J → Type} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)]
    [∀ i, Module R' (M' i)] (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i)
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f _ (fun _ _ ↦ rfl) hf

theorem liftSemi_pullTot1_bijective : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot1 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs h
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add (α T), map_smul' := hs T }
  have ha : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ h T (a T) fun _ ↦ rfl
  have hsh : ∀ T, SemiHom (algebraMap R R') (α T) := fun T ↦
    semiHom_coef (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F') T
  refine _root_.GlobalTheory.liftSemi_prod_bijective R R' _ _ _ _
    (piSL fun T : C ↦ piSL fun T' : C ↦ piSL fun _ : T ⟶ T' ↦ a T')
    (piSL fun T : C ↦ (hsh T).m1) _ (fun _ ↦ rfl) ?_ ?_
  · exact piSL_bij _ fun T ↦ piSL_bij _ fun T' ↦ piSL_bij _ fun _ ↦ ha T'
  · exact piSL_bij _ fun T ↦
      _root_.GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (α T) (hsh T) (a T) (fun _ ↦ rfl) (ha T)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalTwoCochainsFiniteCategoryBaseChangeBijectiv
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TotTwoBaseChange

section Pi

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {J : Type} {M M' : J → Type}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (M' i)] [∀ i, Module R' (M' i)]

def piSL (f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i) : (∀ i, M i) →ₛₗ[algebraMap R R'] (∀ i, M' i) where
  toFun x i := f i (x i)
  map_add' x y := funext fun i ↦ map_add (f i) (x i) (y i)
  map_smul' r x := funext fun i ↦ map_smulₛₗ (f i) r (x i)

theorem piSL_bijective [Finite J] {f : ∀ i, M i →ₛₗ[algebraMap R R'] M' i}
    (hf : ∀ i, Function.Bijective (liftSemi (f i))) : Function.Bijective (liftSemi (piSL f)) :=
  liftSemi_pi_bijective R R' J M M' f (piSL f) (fun _ _ ↦ rfl) hf

end Pi

section Prod

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {M N M' N' : Type}
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R' M'] [AddCommGroup N'] [Module R' N']

def prodSL (f : M →ₛₗ[algebraMap R R'] M') (g : N →ₛₗ[algebraMap R R'] N') :
    (M × N) →ₛₗ[algebraMap R R'] (M' × N') where
  toFun x := (f x.1, g x.2)
  map_add' x y := Prod.ext (map_add f x.1 y.1) (map_add g x.2 y.2)
  map_smul' r x := Prod.ext (map_smulₛₗ f r x.1) (map_smulₛₗ g r x.2)

theorem prodSL_bijective {f : M →ₛₗ[algebraMap R R'] M'} {g : N →ₛₗ[algebraMap R R'] N'}
    (hf : Function.Bijective (liftSemi f)) (hg : Function.Bijective (liftSemi g)) :
    Function.Bijective (liftSemi (prodSL f g)) :=
  liftSemi_prod_bijective R R' M N M' N' f g (prodSL f g) (fun _ ↦ rfl) hf hg

end Prod

theorem main : ∀ (R R' : Type) [CommRing R] [CommRing R'] [Algebra R R'] (C : Type) [Category.{0} C] [Finite C] [∀ T T' : C, Finite (T ⟶ T')] (F : C ⥤ CommAlgCat.{0} R) (F' : C ⥤ CommAlgCat.{0} R') (α : ∀ T : C, F.obj T →+* F'.obj T) (hn : ∀ {T T' : C} (φ : T ⟶ T') (b : F.obj T), α T' (mp F φ b) = mp F' φ (α T b)) (hs : ∀ (T : C) (r : R) (b : F.obj T), α T (r • b) = algebraMap R R' r • α T b), (∀ (T : C) (f : F.obj T →ₛₗ[algebraMap R R'] F'.obj T), (∀ b, f b = α T b) → Function.Bijective (liftSemi f)) → Function.Bijective (liftSemi (pullTot2 (⟨𝟭 C, α, hn, hs⟩ : CoefMap (algebraMap R R') F F'))) := by
  intro R R' _ _ _ C _ _ _ F F' α hn hs H
  let a : ∀ T : C, F.obj T →ₛₗ[algebraMap R R'] F'.obj T := fun T ↦
    { toFun := α T, map_add' := map_add _, map_smul' := hs T }
  have h : ∀ T : C, SemiHom (algebraMap R R') (α T) := hs
  have h0 : ∀ T, Function.Bijective (liftSemi (a T)) := fun T ↦ H T (a T) fun _ ↦ rfl
  have h1 : ∀ T, Function.Bijective (liftSemi (h T).m1) := fun T ↦
    GlobalTheory.kaehler_liftSemi_bijective R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T)
  have h2 : ∀ T, Function.Bijective (liftSemi ((h T).mOm 2)) := fun T ↦
    GlobalTheory.FormsBaseChange.bijective_liftSemi_mOm R R' _ _ (α T) (h T) (a T) (fun _ ↦ rfl) (h0 T) (h1 T) 2
  have k2 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦ piSL_bijective fun T'' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ piSL_bijective fun _ : T' ⟶ T'' ↦ h0 T''
  have k1 := piSL_bijective fun T : C ↦ piSL_bijective fun T' : C ↦
    piSL_bijective fun _ : T ⟶ T' ↦ h1 T'
  have k0 := piSL_bijective h2
  have k := prodSL_bijective k1 k0
  refine liftSemi_prod_bijective R R' (C2 F) (A1 F × W0 F 2) (C2 F') (A1 F' × W0 F' 2) _ _ _ ?_ k2 k
  intro x
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext T T' T'' φ ψ; exact cechDeRhamPullbackTotalDegreeTwo_function_part _ φ ψ x
  · funext T T' φ; exact pullTot2_a _ φ x
  · funext T; exact pullTot2_η _ x T

end GlobalTheory.TotTwoBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TqOfGtCoord
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum
open GlobalTheory.UU GlobalTheory.LN

def tqOfGtCoord {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)
    (hB : IsAbelianScheme (thickObj R I e D.P.A)) : TQ (thickObj R I e G) D.X where
  B := thickObj R I e D.P.A
  isAb := hB
  q := g.q
  i := g.i
  q_hom := g.q_hom
  i_hom := g.i_hom
  q_flat := g.q_flat
  q_surj := g.q_surj
  q_affine := g.q_affine
  isKernel := g.isKernel
  loc b χ := by
    have := g.q_hom
    have := g.i_hom
    let ψ := D.Oφ (D.prBe I e) χ
    have hψ : ∀ k, D.Oφ g.pG χ k = g.q.left ≫ ψ k := fun k => by
      fin_cases k
      · show (padd _ _ _).left = ((Over.map (thick R I e)).map g.q ≫ padd _ _ _).left
        congr 1
        refine Eq.trans ?_ (MonObj.comp_mul _ _ _).symm
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]; rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
      · rfl
      · show (_ ≫ _ : _ ⟶ D.P.A).left = ((Over.map (thick R I e)).map g.q ≫ _ ≫ _).left
        rw [← Category.assoc, toUnit_unique (_ ≫ toUnit _) (toUnit _)]
    choose j hj using fun k => exists_chart D.P.isLB (ψ k b)
    have hle : g.q.left ⁻¹ᵁ LB.wchart D.P.L ψ j ≤ LB.wchart D.P.L (D.Oφ g.pG χ) j := fun x hx =>
      Set.mem_iInter.2 fun k => by rw [hψ]; exact Set.mem_iInter.1 hx k
    refine ⟨LB.wchart D.P.L ψ j, Set.mem_iInter.2 hj, res hle ((g.t χ).s j), fun Z t x h₁ h₂ => ?_⟩
    have ap : ∀ (r : Z.left ⟶ (thickObj R I e G).left) (V) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ((thickObj R I e G).left, V)ˣ)
        (z : Z.left), gm (𝟙 Z.left) z ⊤ (Units.map (r.appLE V ⊤ h).hom.toMonoidHom u) = gm r z V u :=
      fun r V h u z => (gm_res (𝟙 Z.left) z h trivial (pullU r V u)).trans ((gm_pull _ r z V (h trivial) u).trans
        (by rw [Category.id_comp]))
    have key : Units.map (((t ≫ g.i) * x).left.appLE _ ⊤ h₁).hom.toMonoidHom (res hle ((g.t χ).s j)) =
        chV t χ * Units.map (x.left.appLE _ ⊤ h₂).hom.toMonoidHom (res hle ((g.t χ).s j)) := unit_ext fun z _ => by
      obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB z
      have m₁ := h₁ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have m₂ := h₂ (show z ∈ (⊤ : Z.left.Opens) from trivial)
      have hq : ((t ≫ g.i) * x) ≫ g.q = x ≫ g.q := by
        rw [MonObj.mul_comp, Category.assoc, g.isKernel.w, ← Category.assoc,
          toUnit_unique (t ≫ toUnit _) (toUnit Z), ← Hom.one_def, _root_.one_mul]
      have hk : ∀ k, ((t ≫ g.i) * x).left ≫ D.Oφ g.pG χ k = x.left ≫ D.Oφ g.pG χ k := fun k => by
        rw [hψ, ← Category.assoc, ← Category.assoc, ← Over.comp_left, hq, Over.comp_left]
      rw [map_mul, ap, ap]
      refine ((gm_res _ z hle m₁ _).trans (gen_trans (g.t_gen χ) _ z (hle m₁) (hJ.mem _ _))).trans (Eq.trans ?_
        (congrArg (_ * ·) ((gm_res _ z hle m₂ _).trans (gen_trans (g.t_gen χ) _ z (hle m₂) (hJ.mem _ _)))).symm)
      have w := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (g.t_weight χ) (lift t x).left).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))))
      rw [← Over.comp_left, ← Over.comp_left, lift_snd] at w
      have e₁ : lift t x ≫ lift (fst _ _ ≫ g.i) (snd _ _) ≫ μ[thickObj R I e G] = (t ≫ g.i) * x := by
        rw [Hom.mul_def, ← Category.assoc, comp_lift, lift_fst_assoc, lift_snd]
      have e₂ : val (charGen D.X (thickObj R I e G) D.P.L χ) (lift t x).left z J = gm (𝟙 Z.left) z ⊤ (chV t χ) := by
        refine (gm_res _ z _ (hJ.mem _ _) _).trans ((gm_pull _ _ z ⊤ trivial _).trans ?_)
        rw [← Over.comp_left, lift_fst, gm_charUnit]
      rw [e₁, e₂] at w
      refine (congrArg₂ (· * ·) ?_ w).trans (mul_left_comm _ _ _)
      exact Finset.prod_congr rfl fun k _ => congrArg
        (fun q => gm q z (D.P.L.U (j k) ⊓ D.P.L.U (J q)) (D.P.L.g (j k) (J q)) ^ Oinvε k) (hk k)
    exact (congrArg Units.val key).trans (congrArg (· * _) (chV_val t χ))


set_option maxHeartbeats 2000000 in
theorem unif_evenOn : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G],
    IsSemiAbelian G → ∀ U : Unif (maximalIdeal R) D A G, ∃ P : GlobalTheory.UU.CP G, P.L = U.LG ∧ EvenOn P := by
  intro R _ _ _ _ D A G _ _ hS U
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨w, hw⟩ := U.ext
  let U' := GlobalTheory.ValueForm.toPreU U.toUnifPre hL.globalFns hS w hw
  refine ⟨U'.P, rfl, ?_⟩
  obtain ⟨P₀, w₀, h₀⟩ := exists_isLevelCP (maximalIdeal R) 0 U'.P
  obtain ⟨rig, hr, c, σ, h₁, h₂, h₃, H⟩ := exists_isCPMap U'.P (toBase_mul_pullback G (thick R (maximalIdeal R) 0)) _
    (pull_isLB U'.P.L.isLB _) _ (pullIso_isGen U'.P.L.isLB (pullback.fst G.hom (thick R (maximalIdeal R) 0)))
  obtain ⟨w₁, k₁⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm (Category.id_comp _).symm h₀
    (by rw [Category.id_comp, Category.id_comp]; exact pullback.condition)
  obtain ⟨w₂, k₂, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ _ P₀ _ _ _ (𝟙 _) (by simp) _ H).2
    (toBase_mul_of_isMonHom (𝟙 _) _) w₁ k₁
  have H' := GlobalTheory.ClosedPol.isCPMap_w hL.globalFns U' 0 H
  obtain ⟨w₃, -, k₃⟩ := H'.exists_comp k₂ (by rw [Category.id_comp, Category.id_comp]; exact Over.w (U'.gt 0).pG)
  obtain ⟨w₄, k₄⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _) (Category.id_comp _) k₃ (Over.w (U'.gt 0).pG)
  have hB : IsAbelianScheme (thickObj R (maximalIdeal R) 0 D.toPre.P.A) :=
    GlobalTheory.isAbelianScheme_pullback_obj _ _ D.toPre.P.isAb
  let g := U'.gt 0
  have := g.q_hom
  let Q₀ := tqOfGtCoord g hB
  obtain ⟨M₀, v, hv⟩ := exists_isLevelCP (maximalIdeal R) 0 (CP.ofDegPre hL.globalFns D.toPre)
  have hw' : g.q.left ≫ (thickObj R (maximalIdeal R) 0 D.toPre.P.A).hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ :=
    (Over.w g.q).trans (Category.comp_id _).symm
  have hw'' : (g.q.left ≫ pullback.fst D.toPre.P.A.hom (thick R (maximalIdeal R) 0)) ≫ D.toPre.P.A.hom =
      (thickObj R (maximalIdeal R) 0 G).hom ≫ 𝟙 _ ≫ thick R (maximalIdeal R) 0 := by
    exact (Over.w g.pG).trans (congrArg (_ ≫ ·) (Category.id_comp _).symm)
  obtain ⟨w₅, k₅⟩ := GlobalTheory.ClosedPol.cpMap_congr (Category.id_comp _).symm rfl k₄ hw''
  obtain ⟨w₆, k₆, -⟩ := (isCPMap_comp_cancel _ _ _ _ _ _ _ _ _ M₀ P₀ _ _ _ g.q.left hw' hw'' hv).2
    (toBase_mul_of_isMonHom g.q hw') w₅ k₅
  let Dsc : Q₀.Desc P₀ := ⟨M₀, w₆, k₆⟩
  obtain ⟨τ, hτ⟩ := Dsc.exists_even
  exact ⟨D.toPre.X, D.toPre.addX, D.toPre.freeX, D.toPre.finX, Q₀, P₀, ⟨w₀, h₀⟩, τ, hτ⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisUniformiserConsResidualLifts
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FieldPair

open IsLocalRing Polynomial

theorem eq_zero_of_eval_mem_maximalIdeal {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
    {f : R} (hf0 : f ≠ 0) (hfm : f ∈ maximalIdeal R) (p : R[X])
    (hu : ∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) (he : p.eval f = 0) : p = 0 := by
  suffices h : ∀ d (p : R[X]), p.natDegree = d → (∀ i, p.coeff i ≠ 0 → IsUnit (p.coeff i)) →
      p.eval f = 0 → p = 0 from h _ p rfl hu he
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro p hd hu he
  have hsplit := X_mul_divX_add p
  have h2 : p.eval f = f * (divX p).eval f + p.coeff 0 := by
    have h3 := congrArg (Polynomial.eval f) hsplit
    simp only [eval_add, eval_mul, eval_X, eval_C] at h3
    exact h3.symm
  have he' : f * (divX p).eval f + p.coeff 0 = 0 := by rw [← h2]; exact he
  have hc0 : p.coeff 0 = 0 := by
    by_contra hc
    have hmem : p.coeff 0 ∈ maximalIdeal R := by
      have e : p.coeff 0 = -(f * (divX p).eval f) := by linear_combination he'
      rw [e]
      exact (maximalIdeal R).neg_mem ((maximalIdeal R).mul_mem_right _ hfm)
    exact (mem_maximalIdeal _).1 hmem (hu 0 hc)
  have hdv : (divX p).eval f = 0 := by
    rw [hc0, add_zero] at he'
    exact (mul_eq_zero.1 he').resolve_left hf0
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · rw [eq_C_of_natDegree_eq_zero (hd.trans hd0), hc0, C_0]
  · have h0 : divX p = 0 := ih (d - 1) (by omega) (divX p)
      (by rw [natDegree_divX_eq_natDegree_tsub_one, hd])
      (fun i hi => by rw [coeff_divX] at hi ⊢; exact hu _ hi) hdv
    rw [← hsplit, h0, hc0, mul_zero, C_0, add_zero]

theorem trBasis_uniformiser_cons : ∀ {L K : Type} [Field L] [Field K] (cL : ℂ →+* L) (cK : ℂ →+* K)
    (n : ℕ) (S : Place cL) (ψ : S.ring →+* K) (f : S.ring) (w : Fin n → S.ring),
    Function.Surjective ψ → (∀ a, ψ (S.const a) = cK a) → Irreducible f →
    TrBasis cK (fun i => ψ (w i)) →
    TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) ∧
      (fun ω => @dite ℤ (∃ a, S.IsFormOrd ω a) (Classical.propDecidable _) (fun h => h.choose) (fun _ => 0)) (dForm cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L)) = 0 ∧
      S.ord (f : L) = 1 ∧ ∀ g : S.ring, ψ g ≠ 0 → S.ord (g : L) = 0 := by
  intro L K _ _ cL cK n S ψ f w hψ hc hf hwK
  letI : Algebra ℂ S.ring := S.const.toAlgebra
  letI : Algebra ℂ L := cL.toAlgebra
  letI : Algebra ℂ K := cK.toAlgebra
  haveI : IsScalarTower ℂ S.ring L := IsScalarTower.of_algebraMap_eq' rfl
  have hcomp : ψ.comp (algebraMap ℂ S.ring) = algebraMap ℂ K := RingHom.ext hc
  haveI : Algebra.EssFiniteType ℂ S.ring := S.essFiniteType
  haveI := formallySmooth_of_isRegularLocalRing_of_perfectField ℂ S.ring
  have hker : RingHom.ker ψ = maximalIdeal S.ring := by
    haveI := RingHom.ker_isMaximal_of_surjective ψ hψ
    exact IsLocalRing.eq_maximalIdeal this
  have hunit : ∀ g : S.ring, ψ g ≠ 0 → IsUnit g := by
    intro g hg
    by_contra hu
    exact hg (by rw [← RingHom.mem_ker, hker]; exact hu)
  have hwu : ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) w P) := by
    intro P hP
    apply hunit
    rw [MvPolynomial.hom_eval₂, hcomp]
    intro h0
    have hind : AlgebraicIndependent ℂ (fun i => ψ (w i)) := hwK.1
    exact hP ((algebraicIndependent_iff.1 hind) P h0)

  obtain ⟨m, z, b, -, -⟩ := exists_basis_kaehler_uniformiser ℂ hf
  have hL : Algebra.trdeg ℂ L = (m + 1 : ℕ) := trdeg_eq_of_basis_kaehler ℂ L b
  have hR := trdeg_residueField_of_trdeg ℂ S.ring L hL
  simp only [add_tsub_cancel_right] at hR
  have hK : Algebra.trdeg ℂ K = n := by
    have := IsTranscendenceBasis.cardinalMk_eq_trdeg (R := ℂ) hwK
    rw [Cardinal.mk_fin] at this
    exact this.symm
  have hmn : m ≤ n := by
    obtain ⟨s, hs⟩ := exists_isTranscendenceBasis ℂ (ResidueField S.ring)
    let res := IsLocalRing.residue S.ring
    let lift : s → S.ring := fun i => Function.surjInv IsLocalRing.residue_surjective (i : _)
    have hlift : res ∘ lift = Subtype.val := funext fun i =>
      Function.surjInv_eq IsLocalRing.residue_surjective _
    have hg : AlgebraicIndependent ℂ (fun i => ψ (lift i)) := by
      refine algebraicIndependent_iff.2 fun P hP => ?_
      by_contra hne
      have hu : IsUnit (MvPolynomial.eval₂ (algebraMap ℂ S.ring) lift P) := by
        rw [← IsLocalRing.residue_ne_zero_iff_isUnit, MvPolynomial.eval₂_comp_left]
        change MvPolynomial.aeval (res ∘ lift) P ≠ 0
        rw [hlift]
        exact fun h0 => hne (algebraicIndependent_iff.1 hs.1 P h0)
      apply (hu.map ψ).ne_zero
      rw [MvPolynomial.hom_eval₂, hcomp]
      exact hP
    have h1 := hg.cardinalMk_le_trdeg
    rw [hs.cardinalMk_eq_trdeg, hR, hK] at h1
    exact_mod_cast h1

  have hsplit : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P =
        Polynomial.eval f (Polynomial.map (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)
          (MvPolynomial.finSuccEquiv ℂ n P)) := by
    intro P
    have hrh : MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) =
        (Polynomial.evalRingHom f).comp
          ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (algebraMap ℂ S.ring) w)).comp
            (MvPolynomial.finSuccEquiv ℂ n : MvPolynomial (Fin (n + 1)) ℂ →+* _)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [MvPolynomial.finSuccEquiv_apply]
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i <;>
          simp [MvPolynomial.finSuccEquiv_X_zero, MvPolynomial.finSuccEquiv_X_succ]
    exact RingHom.congr_fun hrh P
  have hcoe : ∀ P : MvPolynomial (Fin (n + 1)) ℂ,
      MvPolynomial.aeval (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) P =
        ((MvPolynomial.eval₂ (algebraMap ℂ S.ring) (Fin.cons f w : Fin (n + 1) → S.ring) P :
          S.ring) : L) := by
    intro P
    have h := MvPolynomial.hom_eval₂ P (algebraMap ℂ S.ring) S.ring.subtype
      (Fin.cons f w : Fin (n + 1) → S.ring)
    rw [ValuationSubring.subtype_apply] at h
    rw [h, MvPolynomial.aeval_def]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  have hind : AlgebraicIndependent ℂ (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    refine algebraicIndependent_iff.2 fun P hP => ?_
    rw [hcoe, ZeroMemClass.coe_eq_zero, hsplit] at hP
    set Q := MvPolynomial.finSuccEquiv ℂ n P with hQ
    have hq := eq_zero_of_eval_mem_maximalIdeal hf.ne_zero hf.not_isUnit _ (fun i hi => by
      rw [Polynomial.coeff_map] at hi ⊢
      refine hwu _ fun h0 => hi ?_
      rw [h0, map_zero]) hP
    have hQ0 : Q = 0 := by
      apply Polynomial.ext
      intro i
      rw [Polynomial.coeff_zero]
      by_contra h0
      apply (hwu _ h0).ne_zero
      have := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p i) hq
      simpa [Polynomial.coeff_map] using this
    exact (MvPolynomial.finSuccEquiv ℂ n).injective (by rw [← hQ, hQ0, map_zero])
  have htr : TrBasis cL (Fin.cons (f : L) (fun i => (w i : L)) : Fin (n + 1) → L) := by
    unfold TrBasis
    refine hind.isTranscendenceBasis_of_trdeg_le_of_finite ?_
    rw [hL, Cardinal.mk_fin]
    exact_mod_cast (by omega : m + 1 ≤ n + 1)
  refine ⟨htr, ?_, S.ord_irreducible hf, fun g hg => S.ord_eq_zero (hunit g hg)⟩
  exact GlobalTheory.formOrd_dForm_uniformiser_cons cL n S f w hf hwu ⟨_, htr⟩

end GlobalTheory.FieldPair
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranslateMulInvIsNonvanishingLocusSquare
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.SquareLocus


set_option maxHeartbeats 1000000 in
theorem translate_mul_inv_isLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (V : A.left.Opens), IsLocus c V → ∀ (T : Over S) (a : T ⟶ A), GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull ((a)⁻¹).left c - 2 • GlobalTheory.CechPic.pull (1 : T ⟶ A).left c = 0 → IsLocus (2 • GlobalTheory.CechPic.pull (fst A T).left c) ((fst A T * (snd A T ≫ a)).left ⁻¹ᵁ V ⊓ (fst A T * (snd A T ≫ a)⁻¹).left ⁻¹ᵁ V) := by
  intro S _ A _ hA c V hV T a h
  have hsq := _root_.GlobalTheory.SquareSym.pull_mul_add_pull_mul_inv S A hA c (A ⊗ T) (fst A T) (snd A T ≫ a)
  have e1 : (snd A T ≫ a)⁻¹ = snd A T ≫ a⁻¹ := (GrpObj.comp_inv _ _).symm
  have e2 : (1 : A ⊗ T ⟶ A) = snd A T ≫ (1 : T ⟶ A) := (MonObj.comp_one _).symm
  have h0 : pull (snd A T ≫ a).left c + pull (snd A T ≫ a)⁻¹.left c
      - 2 • pull (1 : A ⊗ T ⟶ A).left c = 0 := by
    rw [e1, e2, Over.comp_left, Over.comp_left, Over.comp_left, pull_comp, pull_comp, pull_comp,
      ← map_nsmul, ← map_add, ← map_sub, h, map_zero]
  have h2 : pull (fst A T * (snd A T ≫ a)).left c + pull (fst A T * (snd A T ≫ a)⁻¹).left c
      = 2 • pull (fst A T).left c := by
    rw [hsq, ← sub_eq_zero, ← h0]
    abel
  have hl := (_root_.GlobalTheory.LocusPull.locus_pull.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)).left c V hV).add
    (_root_.GlobalTheory.LocusPull.locus_pull.1 A.left (A ⊗ T).left (fst A T * (snd A T ≫ a)⁻¹).left c V hV)
  rw [h2] at hl
  exact hl

end GlobalTheory.SquareLocus
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnifTrait
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

def UnifTrait {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (D : DegData R (maximalIdeal R)) (G : Over (Sp R))
    [GrpObj G] (L : LB G.left) : Prop :=
  ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (φ : R →+* W) (G' : Over (Sp W)) (_ : GrpObj G')
    (_ : IsCommMonObj G') (β : G'.left ⟶ G.left) (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W)))
    (U' : Unif (maximalIdeal W) D' A' G'), GlobalTheory.LN.CDvr W ∧ Function.Injective φ ∧ IsLocalHom φ ∧
      IsGrpPullback G' G (spMap φ) β ∧ LBIso U'.LG.L (L.pull β) ∧ Nonempty (IsPullDeg φ D.toPre D'.toPre)

end GlobalTheory.Mum
end
end

