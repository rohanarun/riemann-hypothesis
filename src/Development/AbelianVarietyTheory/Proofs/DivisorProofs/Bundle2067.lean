module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemMaximalIdealExpLeNormVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.ShortVec

theorem nonneg_of_tendsto {X : Type} [AddCommGroup X] (q : QuadraticMap ℤ X ℝ)
    (hq : Filter.Tendsto q Filter.cofinite Filter.atTop) (a : X) : 0 ≤ q a := by
  by_contra h
  have h : q a < 0 := not_le.1 h
  have hfin : {x | ¬ (0 : ℝ) ≤ q x}.Finite := Filter.eventually_cofinite.1 (hq.eventually_ge_atTop 0)
  have hv : ∀ n : ℕ, q (((n : ℤ) + 1) • a) = ((n : ℝ) + 1) ^ 2 * q a := fun n => by
    rw [QuadraticMap.map_smul, zsmul_eq_mul]
    push_cast
    ring
  refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n : ℤ) + 1) • a) (fun m n e => ?_)
    (fun n => ?_) hfin
  · have e' := congrArg q e
    simp only [hv] at e'
    have e2 := mul_right_cancel₀ h.ne e'
    have e3 := (pow_left_inj₀ (by positivity) (by positivity) two_ne_zero).1 e2
    exact_mod_cast add_right_cancel e3
  · simp only [Set.mem_setOf_eq, hv, not_le]
    exact mul_neg_of_pos_of_neg (by positivity) h

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {M : RatModel o Ω}

theorem val_mul_gen {p : ℕ} [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) {a b : Ω}
    (ha : a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hb : b ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) :
    M.val (gPt p ≫ y) (a * b) = M.val (gPt p ≫ y) a * M.val (gPt p ≫ y) b :=
  RatModel.val_mul (RatModel.specializes_of_range_eq (RatModel.range_eq_singleton _ _)) ha hb

theorem norm_th_eq_and_HH_eq {z : M.Z} {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p}
    (hc : y (cPt p) = z) (hR : ∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p))))
    (hAt : S.At M y y₀) (τ : S.Test p y₀) {x₀ : S.Gam} (hx₀ : M.Div S.th x₀ z) :
    ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ ∧ S.HH M z = τ.yy.ker := by
  have hsp := RatModel.gPt_specializes hc (IsLocalRing.closedPoint (PadicAlgCl p))
  have hy : ∀ x, y₀ ⟨S.th x, S.th_mem x⟩ = M.val (gPt p ≫ y) (S.th x) := fun x => hAt _
  have hmul : ∀ x, ‖M.val (gPt p ≫ y) (S.th x)‖ =
      ‖M.val (gPt p ≫ y) (S.th x / S.th x₀)‖ * ‖M.val (gPt p ≫ y) (S.th x₀)‖ := by
    intro x
    rw [← norm_mul, ← val_mul_gen y (RatModel.O_le_of_specializes hsp (hx₀.2 x))
      (hR _ (S.th_mem x₀)), div_mul_cancel₀ _ hx₀.1]
  have hδ : ‖M.val (gPt p ≫ y) (S.th x₀)‖ = τ.δ := by
    apply le_antisymm
    · rw [← hy]
      exact τ.δ_max.2 ⟨x₀, rfl⟩
    · obtain ⟨x₁, hx₁⟩ := τ.δ_max.1
      simp only [hy] at hx₁
      rw [← hx₁, hmul x₁]
      exact mul_le_of_le_one_left (norm_nonneg _) (RatModel.norm_val_le_one hc (hx₀.2 x₁))
  have key : ∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ := by
    intro x
    change M.Div S.th x z ↔ _
    rw [hx₀.div_iff_isUnit x, ← RatModel.norm_val_eq_one_iff hc (hx₀.2 x), hmul x, hδ]
    exact (mul_eq_right₀ τ.δ_pos.ne').symm
  refine ⟨hδ, ?_⟩
  rw [← τ.supp, ThetaSys.HH]
  congr 1
  ext x
  rw [key x, Set.mem_setOf_eq, hy]

theorem exists_open (S : ThetaSys o Ω) (M : RatModel o Ω) (b : Ω) :
    ∃ U : M.Z.Opens, (U : Set M.Z).Nonempty ∧ S.R ≤ M.ringOn U ∧ b ∈ M.ringOn U := by
  obtain ⟨s, hs⟩ := S.fg
  refine ⟨⟨{z | b ∈ M.O z} ∩ ⋂ a ∈ s, {z | a ∈ M.O z},
    (M.isOpen_setOf_mem_O b).inter (isOpen_biInter_finset fun a _ => M.isOpen_setOf_mem_O a)⟩,
    ⟨genericPoint M.Z, ?_, ?_⟩, ?_, RatModel.mem_ringOn.2 fun z hz => hz.1⟩
  · simp [RatModel.O_genericPoint]
  · simp [RatModel.O_genericPoint]
  · rw [← hs]
    exact Algebra.adjoin_le fun a ha => RatModel.mem_ringOn.2 fun z hz => Set.mem_iInter₂.1 hz.2 a ha

end GlobalTheory.ShortVec

namespace GlobalTheory

open ShortVec

theorem exists_mem_maximalIdeal_exp_le_norm_val :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω),
    IsNormalScheme M.Z → M.HasDiv S.th → S.HasTests → ∀ (z₁ : M.Z), IsClosed ({z₁} : Set M.Z) →
    ∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p), y (cPt p) = z₁ →
    (∀ a ∈ S.R, a ∈ M.O ((gPt p ≫ y) (IsLocalRing.closedPoint (PadicAlgCl p)))) → S.At M y y₀ →
    ∀ (τ : S.Test p y₀) (α : τ.X), (∀ v0, τ.q α ≤ τ.q (α + S.N • v0)) → 0 < τ.q α →
    ∃ h ∈ maximalIdeal (M.Z.presheaf.stalk z₁),
      Real.exp (-(τ.q α / S.N)) ≤ ‖M.val (gPt p ≫ y) (M.stalkHom z₁ h)‖ := by
  intro o Ω _ _ _ hb S M hn hd hT z hz p _ y y₀ hc hR hAt τ α hα hpos
  haveI := hb.ft
  haveI := hb.char
  obtain ⟨j, hj⟩ := hd z
  obtain ⟨hδ, hH⟩ := norm_th_eq_and_HH_eq hc hR hAt τ hj
  obtain ⟨k, hk, he⟩ := τ.eq α hα
  obtain ⟨U, hU, hRU, hbU⟩ := exists_open S M (S.FF _ (τ.wt α) k / S.th j)
  have hreg : S.FF _ (τ.wt α) k / S.th j ∈ M.O z := by
    refine ((classical_points_and_local_regularity o Ω M U fun x => ⟨hn.1 x, hn.2 x⟩).1 U le_rfl hU z hz).2 _ hbU fun p' _ y' hy' => ?_
    let w : Sp (PadicAlgCl p') := IsLocalRing.closedPoint (PadicAlgCl p')
    have hw : (gPt p' ≫ y') w ∈ (U : Set M.Z) := hy'.2 ⟨w, rfl⟩
    have hle : S.R ≤ M.O ((gPt p' ≫ y') w) := hRU.trans (RatModel.ringOn_le_O hw)
    let y₀' : S.R →+* PadicAlgCl p' :=
      (RatModel.valHom (gPt p' ≫ y') _ (RatModel.range_eq_singleton _ w)).comp (Subalgebra.inclusion hle).toRingHom
    have hint : ∀ a : o, ‖y₀' (algebraMap o S.R a)‖ ≤ 1 := fun a =>
      hy'.norm_val_le_one (x := algebraMap o Ω a) ((M.O z).algebraMap_mem a)
    have hAt' : S.At M y' y₀' := fun _ => rfl
    obtain ⟨τ'⟩ := hT p' y₀' hint
    obtain ⟨hδ', hH'⟩ := norm_th_eq_and_HH_eq hy'.1 (fun a ha => hle ha) hAt' τ' hj
    obtain ⟨β, -, -, hβ⟩ := (thetaSys_norm_FF_le_exp o Ω S (test_weights o Ω S) p' y₀' τ' hint _ (τ.wt α) k hk
      τ.isoFree).2 (by rw [← hH', hH])
    have hexp : Real.exp (-(τ'.q β / S.N)) ≤ 1 :=
      Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (nonneg_of_tendsto _ τ'.pos β) (Nat.cast_nonneg _)))
    have hmul := val_mul_gen y' (RatModel.ringOn_le_O hw hbU) (hle (S.th_mem j))
    rw [div_mul_cancel₀ _ hj.1] at hmul
    rw [hAt'] at hβ
    change ‖M.val (gPt p' ≫ y') (S.FF _ (τ.wt α) k)‖ ≤ _ at hβ
    rw [hmul, norm_mul, hδ', mul_comm] at hβ
    exact (le_of_mul_le_mul_left hβ τ'.δ_pos).trans hexp
  have hmul := val_mul_gen y (RatModel.O_le_of_specializes (RatModel.gPt_specializes hc _) hreg) (hR _ (S.th_mem j))
  rw [div_mul_cancel₀ _ hj.1] at hmul
  rw [hAt] at he
  change ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k)‖ = _ at he
  rw [hmul, norm_mul, hδ, mul_comm] at he
  have he' := mul_left_cancel₀ τ.δ_pos.ne' he
  have hN : (0 : ℝ) < S.N := by
    have := S.N_ge
    exact_mod_cast (by omega : 0 < S.N)
  have hlt : ‖M.val (gPt p ≫ y) (S.FF _ (τ.wt α) k / S.th j)‖ < 1 := by
    rw [he']
    exact Real.exp_lt_one_iff.2 (neg_neg_of_pos (div_pos hpos hN))
  have hnu := (RatModel.norm_val_lt_one_iff hc hreg).1 hlt
  refine ⟨(M.stalkEquiv z).symm ⟨_, hreg⟩, ?_, ?_⟩
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MulEquiv.isUnit_map]
    exact hnu
  · rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply]
    exact he'.ge

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMorphismLiftSystemPresentsOfHom
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.LiftSys.Glue

open Opposite _root_.CategoryTheory.Limits

theorem spMap_comp₂ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp]; rfl

theorem spMap_surjective {A B : Type} [CommRing A] [CommRing B] (q : A →+* B)
    (hq : Function.Surjective q) (hn : ∀ a, q a = 0 → a * a = 0) : Function.Surjective (spMap q) := by
  intro p
  have hker : RingHom.ker q ≤ p.asIdeal := by
    intro x hx
    have hx2 := hn x (RingHom.mem_ker.1 hx)
    exact (p.isPrime.mem_or_mem (by rw [hx2]; exact p.asIdeal.zero_mem)).elim id id
  haveI := p.isPrime
  haveI : (Ideal.map q p.asIdeal).IsPrime := Ideal.map_isPrime_of_surjective hq hker
  refine ⟨⟨Ideal.map q p.asIdeal, this⟩, ?_⟩
  apply PrimeSpectrum.ext
  change Ideal.comap q (Ideal.map q p.asIdeal) = p.asIdeal
  rw [Ideal.comap_map_of_surjective _ hq, sup_eq_left]
  intro x hx
  exact hker (by simpa [RingHom.mem_ker] using hx)

theorem exists_affine {X₀ : Scheme.{0}} {x : X₀} {U : X₀.Opens} (hx : x ∈ U) :
    ∃ W : X₀.affineOpens, x ∈ W.1 ∧ W.1 ≤ U := by
  obtain ⟨W, hW, hxW, hWU⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₀.isBasis_affineOpens) hx
  exact ⟨⟨W, hW⟩, hxW, hWU⟩

variable {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} {π : R →+* R₀} {X₀ : Scheme.{0}}
  {s₀ : X₀ ⟶ Sp R₀}

abbrev cov {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x) :
    X.OpenCover where
  I₀ := X₀.affineOpens
  X U := Sp (S.F.obj (op U))
  f U := h.y (op U)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨fun x ↦ by obtain ⟨U, z, hz⟩ := hc x; exact ⟨U, z, hz⟩, fun U ↦ h.isOpen _⟩

def dir {S : Sys I π s₀} {X : Scheme.{0}} {s : X ⟶ Sp R} {i : X₀ ⟶ X} (h : S.Presents s i)
    (hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S.F.obj (op U))), h.y (op U) z = x)
    (hd : ∀ (U V : X₀.affineOpens) (a : Sp (S.F.obj (op U))) (b : Sp (S.F.obj (op V))),
      h.y (op U) a = h.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S.F.obj (op W))), h.y (op W) c = h.y (op U) a) :
    (cov h hc).LocallyDirected where
  trans {U V} a := spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U))
  trans_id U := by
    haveI := h.isOpen (op U)
    rw [← cancel_mono (h.y (op U))]
    exact (h.nat _).trans (Category.id_comp _).symm
  trans_comp {U V W} a b := by
    haveI := h.isOpen (op W)
    rw [← cancel_mono (h.y (op W))]
    rw [Category.assoc, h.nat, h.nat, h.nat]
  w {U V} a := h.nat a.op
  directed {U V} x := by
    haveI := h.isOpen (op U)
    haveI := h.isOpen (op V)
    obtain ⟨W, hWU, hWV, c, hcW⟩ := hd U V (pullback.fst (h.y (op U)) (h.y (op V)) x)
      (pullback.snd (h.y (op U)) (h.y (op V)) x)
      (by rw [← Scheme.Hom.comp_apply, pullback.condition, Scheme.Hom.comp_apply])
    refine ⟨W, homOfLE hWU, homOfLE hWV, c, ?_⟩
    apply (pullback.fst (h.y (op U)) (h.y (op V)) ≫ h.y (op U)).isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, pullback.lift_fst_assoc]
    change (spMap _ ≫ h.y (op U)) c = _
    rw [h.nat, hcW, Scheme.Hom.comp_apply]
  property_trans {U V} a := by
    haveI := h.isOpen (op V)
    haveI : IsOpenImmersion (spMap (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) ≫ h.y (op V)) := by
      rw [h.nat]; exact h.isOpen _
    exact IsOpenImmersion.of_comp _ (h.y (op V))

theorem presents_hom : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀), ∀ (S S' : Sys I π s₀) (X : Scheme.{0}) (s : X ⟶ Sp R) (i : X₀ ⟶ X) (Y : Scheme.{0}) (t : Y ⟶ Sp R) (j : X₀ ⟶ Y), IsPullback i s₀ s (spMap π) → S.Presents t j → S'.Presents s i → (∃ ψ : ∀ U, S.F.obj U →ₐ[R] S'.F.obj U, (∀ U b, S'.p U (ψ U b) = S.p U b) ∧ ∀ (U V : AffOp X₀) (a : U ⟶ V) (b : S.F.obj U), mp S'.F a (ψ U b) = ψ V (mp S.F a b)) → ∃ f : X ⟶ Y, f ≫ t = s ∧ i ≫ f = j := by
  intro R R₀ _ _ I hI π hπ hk X₀ s₀ S S' X s i Y t j hpb hY hX hψ
  obtain ⟨ψ, hψp, hψn⟩ := hψ

  have hsurU : ∀ U, Function.Surjective (spMap (S'.p U)) := fun U ↦
    spMap_surjective _ (S'.surj U) fun b hb ↦ by
      have hb' := (S'.ker U b).1 hb
      have : b * b ∈ (I.map (algebraMap R (S'.F.obj U))) ^ 2 := by
        rw [pow_two]; exact Ideal.mul_mem_mul hb' hb'
      rwa [map_sq hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  have hπs : Function.Surjective (spMap π) := spMap_surjective π hπ fun a ha ↦ by
    have ha' : a ∈ I := hk ▸ RingHom.mem_ker.2 ha
    have : a * a ∈ I ^ 2 := by rw [pow_two]; exact Ideal.mul_mem_mul ha' ha'
    rwa [hI, Ideal.zero_eq_bot, Ideal.mem_bot] at this

  haveI : IsClosedImmersion (spMap π) := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom π) hπ
  haveI hic : IsClosedImmersion i := MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip inferInstance
  have hinj : Function.Injective i := i.isClosedEmbedding.injective
  have hisurj : Function.Surjective i :=
    (MorphismProperty.of_isPullback (P := @AlgebraicGeometry.Surjective) hpb.flip ⟨hπs⟩).surj

  have hrng : ∀ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), ∃ x₀ ∈ U.1, hX.y (op U) z = i x₀ := by
    intro U z
    obtain ⟨w, rfl⟩ := hsurU (op U) z
    refine ⟨affPt s₀ U w, U.2.range_fromSpec.le ⟨w, rfl⟩, ?_⟩
    rw [← Scheme.Hom.comp_apply, hX.red (op U), Scheme.Hom.comp_apply]
  have hcov : ∀ (U : X₀.affineOpens) (x₀ : X₀), x₀ ∈ U.1 → ∃ z : Sp (S'.F.obj (op U)), hX.y (op U) z = i x₀ := by
    intro U x₀ hx
    obtain ⟨w, hw⟩ : x₀ ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hx
    refine ⟨spMap (S'.p (op U)) w, ?_⟩
    change (spMap (S'.p (op U)) ≫ hX.y (op U)) w = i x₀
    rw [hX.red (op U), Scheme.Hom.comp_apply]
    exact congrArg i hw
  have hc : ∀ x : X, ∃ (U : X₀.affineOpens) (z : Sp (S'.F.obj (op U))), hX.y (op U) z = x := by
    intro x
    obtain ⟨x₀, rfl⟩ := hisurj x
    obtain ⟨U, hxU, -⟩ := exists_affine (show x₀ ∈ (⊤ : X₀.Opens) from trivial)
    obtain ⟨z, hz⟩ := hcov U x₀ hxU
    exact ⟨U, z, hz⟩
  have hd : ∀ (U V : X₀.affineOpens) (a : Sp (S'.F.obj (op U))) (b : Sp (S'.F.obj (op V))),
      hX.y (op U) a = hX.y (op V) b → ∃ (W : X₀.affineOpens) (_ : W ≤ U) (_ : W ≤ V)
        (c : Sp (S'.F.obj (op W))), hX.y (op W) c = hX.y (op U) a := by
    intro U V a b hab
    obtain ⟨x₀, hxU, ha⟩ := hrng U a
    obtain ⟨x₁, hxV, hb⟩ := hrng V b
    have e : x₀ = x₁ := hinj (ha.symm.trans (hab.trans hb))
    subst e
    obtain ⟨W, hxW, hWle⟩ := exists_affine (show x₀ ∈ U.1 ⊓ V.1 from ⟨hxU, hxV⟩)
    obtain ⟨c, hc'⟩ := hcov W x₀ hxW
    exact ⟨W, le_inf_iff.1 hWle |>.1, le_inf_iff.1 hWle |>.2, c, hc'.trans ha.symm⟩
  letI := dir hX hc hd
  let 𝒰 := cov hX hc
  let g : ∀ U : 𝒰.I₀, 𝒰.X U ⟶ Y := fun U ↦
    spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)
  have hg : ∀ {U V : 𝒰.I₀} (a : U ⟶ V), 𝒰.trans a ≫ g V = g U := by
    intro U V a
    change spMap (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)) ≫
      spMap (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) ≫ hY.y (op V) = _
    rw [← Category.assoc, ← spMap_comp₂]
    have e : (mp S'.F a.op : S'.F.obj (op V) →+* S'.F.obj (op U)).comp
        (ψ (op V) : S.F.obj (op V) →+* S'.F.obj (op V)) =
        (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)).comp
          (mp S.F a.op : S.F.obj (op V) →+* S.F.obj (op U)) :=
      RingHom.ext fun b ↦ hψn (op V) (op U) a.op b
    rw [e, spMap_comp₂, Category.assoc, hY.nat a.op]
  refine ⟨𝒰.glueMorphismsOfLocallyDirected g hg, 𝒰.hom_ext _ _ fun U ↦ ?_, ?_⟩
  · rw [𝒰.map_glueMorphismsOfLocallyDirected_assoc g hg U]
    change (spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U)) ≫ t = hX.y (op U) ≫ s
    rw [Category.assoc, hY.base, hX.base, ← spMap_comp₂]
    exact congrArg spMap (RingHom.ext fun r ↦ (ψ (op U)).commutes r)
  · let 𝒱 : X₀.OpenCover := Scheme.Cover.mkOfCovers X₀.affineOpens (fun U ↦ Sp (Sec s₀ U.1))
      (fun U ↦ affPt s₀ U)
      (fun x ↦ by
        obtain ⟨U, hxU, -⟩ := exists_affine (show x ∈ (⊤ : X₀.Opens) from trivial)
        obtain ⟨w, hw⟩ : x ∈ Set.range (affPt s₀ U) := U.2.range_fromSpec.ge hxU
        exact ⟨U, w, hw⟩)
      (fun U ↦ IsAffineOpen.isOpenImmersion_fromSpec U.2)
    refine 𝒱.hom_ext _ _ fun U ↦ ?_
    change affPt s₀ U ≫ i ≫ _ = affPt s₀ U ≫ j
    rw [← Category.assoc, show affPt s₀ U ≫ i = _ from (hX.red (op U)).symm,
      show affPt s₀ U ≫ j = _ from (hY.red (op U)).symm, Category.assoc]
    change spMap (S'.p (op U)) ≫ 𝒰.f U ≫ _ = _
    rw [𝒰.map_glueMorphismsOfLocallyDirected g hg U]
    change spMap (S'.p (op U)) ≫ spMap (ψ (op U) : S.F.obj (op U) →+* S'.F.obj (op U)) ≫ hY.y (op U) = _
    rw [← Category.assoc, ← spMap_comp₂]
    exact congrArg (· ≫ hY.y (op U)) (congrArg spMap (RingHom.ext fun b ↦ hψp (op U) b))

end GlobalTheory.LiftSys.Glue
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulPowMemCartierMultipleOfRegularLocus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem regAt_pow_of_regAt {Y : Scheme.{0}} [IsIntegral Y] {y : Y} {u : Y.functionField} (h : RegAt y u) (n : ℕ) :
    RegAt y (u ^ n) :=
  have ⟨a, ha⟩ := h; ⟨a ^ n, by rw [map_pow, ha]⟩

theorem exists_regAt_mul_pow_affine {Y : Scheme.{0}} [IsIntegral Y] {U : Y.Opens} (hU : IsAffineOpen U)
    (hg : genericPoint Y ∈ U) {u g : Y.functionField} (hu0 : u ≠ 0) (hu : ∀ y ∈ U, RegAt y u)
    (h : ∀ y ∈ U, UnitAt y u → RegAt y g) : ∃ n : ℕ, ∀ y ∈ U, RegAt y (g * u ^ n) := by
  obtain ⟨f, rfl⟩ := exists_fnOf_eq hg hu
  have hb : genericPoint Y ∈ Y.basicOpen f := (unitAt_fnOf_iff hg hg f).1 (unitAt_genericPoint hu0)
  obtain ⟨b, rfl⟩ := exists_fnOf_eq hb fun y hy =>
    h y (Y.basicOpen_le f hy) ((unitAt_fnOf_iff (Y.basicOpen_le f hy) hg f).2 hy)
  have := hU.isLocalization_basicOpen f
  obtain ⟨⟨a, _, n, rfl⟩, e⟩ := IsLocalization.surj (Submonoid.powers f) b
  refine ⟨n, fun y hy => ?_⟩
  have e' := congrArg (fnOf _ hb) e
  have r (c : Γ(Y, U)) : fnOf _ hb (algebraMap Γ(Y, U) Γ(Y, Y.basicOpen f) c) = fnOf U hg c :=
    fnOf_resG (Y.basicOpen_le f) hb c
  simp only [map_mul, r] at e'
  rw [map_pow] at e'
  rw [e']
  exact regAt_fnOf hy hg a

theorem exists_mul_pow_mem_sec (Y : Scheme.{0}) [IsIntegral Y] [CompactSpace Y] (D : CartierDiv Y) (k : ℕ)
    (s : Y.functionField) (hs : s ∈ Sec D k) (g : Y.functionField) (hg : ∀ y ∈ locus D k s, RegAt y g) :
    ∃ n : ℕ, g * s ^ n ∈ Sec D (k * n) := by
  by_cases hs0 : s = 0
  · refine ⟨1, fun x => ?_⟩
    rw [hs0, pow_one, mul_zero]
    exact (CartierDiv.vanishesAt_zero _ x).regularAt
  have key (x : Y) : ∃ U : Y.Opens, x ∈ U ∧ ∃ n : ℕ, ∀ m, n ≤ m → ∀ y ∈ U,
      ((k * m) • D).RegularAt y (g * s ^ m) := by
    obtain ⟨V, hV, e, he⟩ := (k • D).exists_isEqn_nhds x
    obtain ⟨U, hU, hx, hUV⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens hV
    have hu (y) (hy : y ∈ U) : RegAt y (s * e) := (he y (hUV hy)).regularAt_iff.1 (hs y)
    obtain ⟨n, hn⟩ := exists_regAt_mul_pow_affine (g := g) hU (gen_mem hx) (mul_ne_zero hs0 e.ne_zero) hu
      fun y hy h => hg y ⟨e, he y (hUV hy), h⟩
    refine ⟨U, hx, n, fun m hm y hy => ?_⟩
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [mul_nsmul]
    refine ⟨_, (he y (hUV hy)).nsmul _, ?_⟩
    have := (hn y hy).mul (regAt_pow_of_regAt (hu y hy) d)
    rwa [_root_.mul_assoc, ← pow_add, mul_pow, ← _root_.mul_assoc, ← Units.val_pow_eq_pow_val] at this
  choose U hU n hn using key
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set Y)) (fun x => (U x).isOpen)
    fun x _ => Set.mem_iUnion.2 ⟨x, hU x⟩
  refine ⟨t.sup n, fun y => ?_⟩
  obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
  exact hn x _ (Finset.le_sup hx) y hy

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenOfSaturatedLocalSchemeBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc

theorem exists_open_of_saturated_stalkBaseChange : ∀ (S S₁ P : Scheme.{0}) (p : P ⟶ S) (x : S) (ξ' : S₁ ⟶ Spec (S.presheaf.stalk x)) (ξ : S₁ ⟶ S), ξ' ≫ S.fromSpecStalk x = ξ → Flat ξ' → Surjective ξ' → QuasiCompact ξ' → ∀ O : Set ↥(Limits.pullback p ξ), IsOpen O → (∀ w w' : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w = Limits.pullback.fst p ξ w' → w ∈ O → w' ∈ O) → ∃ V : P.Opens, ∀ w : ↥(Limits.pullback p ξ), Limits.pullback.fst p ξ w ∈ V ↔ w ∈ O := by
  intro S S₁ P p x ξ' ξ hξ hfl hsu hqc O hO hsat
  subst hξ
  obtain ⟨π, hπ, hπ2⟩ : ∃ π : pullback p (ξ' ≫ S.fromSpecStalk x) ⟶ pullback p (S.fromSpecStalk x),
      π ≫ pullback.fst p (S.fromSpecStalk x) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) ∧
      π ≫ pullback.snd p (S.fromSpecStalk x) = pullback.snd p (ξ' ≫ S.fromSpecStalk x) ≫ ξ' :=
    ⟨pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ ξ') (by rw [Category.assoc]; exact pullback.condition),
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  have hsq : IsPullback π (pullback.snd p (ξ' ≫ S.fromSpecStalk x)) (pullback.snd p (S.fromSpecStalk x)) ξ' := by
    refine IsPullback.of_right ?_ hπ2 (IsPullback.of_hasPullback p (S.fromSpecStalk x))
    rw [hπ]
    exact IsPullback.of_hasPullback p (ξ' ≫ S.fromSpecStalk x)
  have : Flat π := MorphismProperty.of_isPullback (P := @Flat) hsq.flip hfl
  have : Surjective π := MorphismProperty.of_isPullback (P := @Surjective) hsq.flip hsu
  have : QuasiCompact π := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq.flip hqc
  have hq := Flat.isQuotientMap_of_surjective π
  have hc : ∀ w, pullback.fst p (S.fromSpecStalk x) (π w) = pullback.fst p (ξ' ≫ S.fromSpecStalk x) w := by
    intro w; rw [← Scheme.Hom.comp_apply, hπ]
  have hpre : π ⁻¹' (π '' O) = O := by
    ext w; constructor
    · rintro ⟨w', hw', he⟩
      exact hsat w' w (by rw [← hc, ← hc, he]) hw'
    · intro hw; exact ⟨w, hw, rfl⟩
  have hopen : IsOpen (π '' O) := by
    rw [← hq.isOpen_preimage, hpre]; exact hO
  have hemb := IsPreimmersion.isEmbedding (pullback.fst p (S.fromSpecStalk x))
  obtain ⟨t, ht, hte⟩ := hemb.isInducing.isOpen_iff.1 hopen
  refine ⟨⟨t, ht⟩, fun w => ?_⟩
  change _ ∈ t ↔ _
  rw [← hc, ← Set.mem_preimage, hte, ← Set.mem_preimage, hpre]

end GlobalTheory.Desc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRatioUnitOfLineBundleGeneratorsOnOpens
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchLift

theorem exists_ratio_unit : ∀ (Y : Scheme.{0}) (L : LB Y), L.IsLB → ∀ (O₁ O₂ : Y.Opens) (s₁ : ∀ k, Γ(Y, L.U k ⊓ O₁)ˣ) (s₂ : ∀ k, Γ(Y, L.U k ⊓ O₂)ˣ), GlobalTheory.PinchLift.GenOn L O₁ s₁ → GlobalTheory.PinchLift.GenOn L O₂ s₂ → ∃ r : Γ(Y, O₁ ⊓ O₂)ˣ, ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k → f t ∈ O₁ → f t ∈ O₂ → gm f t (O₁ ⊓ O₂) r = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
  intro Y L hL O₁ O₂ s₁ s₂ h₁ h₂
  have hW : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ O₁ ⊓ O₂ := fun k => inf_le_right
  have hc : O₁ ⊓ O₂ ≤ ⨆ k, L.U k ⊓ (O₁ ⊓ O₂) := fun y hy => by
    obtain ⟨k, hk⟩ := exists_chart hL y
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨k, hk, hy⟩
  have i₁ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₁ := fun k => inf_le_inf_left _ inf_le_left
  have i₂ : ∀ k, L.U k ⊓ (O₁ ⊓ O₂) ≤ L.U k ⊓ O₂ := fun k => inf_le_inf_left _ inf_le_right
  let u : ∀ k, Γ(Y, L.U k ⊓ (O₁ ⊓ O₂))ˣ := fun k => res (i₁ k) (s₁ k) * (res (i₂ k) (s₂ k))⁻¹
  have hu : ∀ (T : Scheme.{0}) (f : T ⟶ Y) (t : T) (k : L.ι), f t ∈ L.U k ⊓ (O₁ ⊓ O₂) →
      gm f t (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm f t (L.U k ⊓ O₁) (s₁ k) * (gm f t (L.U k ⊓ O₂) (s₂ k))⁻¹ := by
    intro T f t k hy
    simp only [u, map_mul, map_inv, gm_res f t (i₁ k) hy, gm_res f t (i₂ k) hy]
  obtain ⟨r, hr⟩ := glue_unit (O₁ ⊓ O₂) (fun k => L.U k ⊓ (O₁ ⊓ O₂)) hW hc u (by
    intro k l y hy
    have hk : y ∈ L.U k ⊓ (O₁ ⊓ O₂) := hy.1
    have hl : y ∈ L.U l ⊓ (O₁ ⊓ O₂) := hy.2
    show gm (𝟙 Y) y (L.U k ⊓ (O₁ ⊓ O₂)) (u k) = gm (𝟙 Y) y (L.U l ⊓ (O₁ ⊓ O₂)) (u l)
    rw [hu Y (𝟙 Y) y k hk, hu Y (𝟙 Y) y l hl, h₁ k l y hk.1 hl.1 hk.2.1, h₂ k l y hk.1 hl.1 hk.2.2,
      ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_left_eq_div])
  refine ⟨r, fun T f t k hk ht₁ ht₂ => ?_⟩
  have hy : f t ∈ L.U k ⊓ (O₁ ⊓ O₂) := ⟨hk, ht₁, ht₂⟩
  rw [← gm_res f t (hW k) hy r, hr k, hu T f t k hy]

end GlobalTheory.PinchLift
end
end

