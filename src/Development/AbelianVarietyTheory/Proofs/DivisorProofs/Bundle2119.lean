module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.SurjectiveOfIsPullbackSqZero
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsNoetherianRingDualNumber
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.EqOfAgreeOnTorsion
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsAmpleLBOfRelAmpleOfIsAffine
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SummandDualAnnihilatorReductionProjective
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham GlobalTheory.SqLift GlobalTheory.LiftSys GlobalTheory.Published
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualSummand

open Module _root_.Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]

theorem isCompl_dualAnnihilator {K N : Submodule R C} (h : IsCompl K N) :
    IsCompl K.dualAnnihilator N.dualAnnihilator := by
  constructor
  · rw [disjoint_iff, eq_bot_iff]
    intro f hf
    rw [mem_inf, mem_dualAnnihilator, mem_dualAnnihilator] at hf
    rw [mem_bot]
    ext c
    rw [← projection_add_projection_eq_self h c, map_add (f := _), hf.1 _ (projection_apply_mem h c),
      hf.2 _ (projection_apply_mem h.symm c)]
    simp
  · rw [codisjoint_iff, eq_top_iff]
    intro f _
    have e : f = f ∘ₗ N.projection K h.symm + f ∘ₗ K.projection N h := by
      ext c
      simp only [LinearMap.add_apply, LinearMap.comp_apply]
      rw [← map_add (f := _), add_comm, projection_add_projection_eq_self h c]
    rw [e]
    refine add_mem_sup ?_ ?_
    · rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk]
    · rw [mem_dualAnnihilator]
      intro n hn
      simp [projection_apply_of_mem_right h hn]

theorem dualAnnihilator_dualCoannihilator_eq [Projective R C] {K N : Submodule R C}
    (h : IsCompl K N) : K.dualAnnihilator.dualCoannihilator = K := by
  refine le_antisymm (fun c hc => ?_) (le_dualAnnihilator_dualCoannihilator _)
  rw [mem_dualCoannihilator] at hc
  have hn : N.projection K h.symm c = 0 := by
    rw [← forall_dual_apply_eq_zero_iff R]
    intro φ
    have := hc (φ ∘ₗ N.projection K h.symm) (by
      rw [mem_dualAnnihilator]
      intro k hk
      simp [projection_apply_of_mem_right h.symm hk])
    simpa using this
  rw [← projection_add_projection_eq_self h c, hn, add_zero]
  exact projection_apply_mem h c

theorem mem_smul_top_of_forall_dual [Projective R C] (I : Ideal R) (c : C)
    (h : ∀ x : Dual R C, x c ∈ I) : c ∈ I • (⊤ : Submodule R C) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  rw [← hs c, Finsupp.linearCombination_apply, Finsupp.sum]
  refine Submodule.sum_mem _ fun m _ => ?_
  exact smul_mem_smul (by simpa using h (Finsupp.lapply m ∘ₗ s)) mem_top

variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem exists_dual_lift [Projective R C] (hπ : Function.Surjective π) (ρ : C →ₛₗ[π] C₀)
    (y : Dual R₀ C₀) : ∃ x : Dual R C, ∀ c, π (x c) = y (ρ c) := by
  obtain ⟨s, hs⟩ := projective_def.mp (inferInstance : Projective R C)
  refine ⟨Finsupp.linearCombination R (fun m => Function.surjInv hπ (y (ρ m))) ∘ₗ s, fun c => ?_⟩
  conv_rhs => rw [← hs c]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [LinearMap.comp_apply, Finsupp.linearCombination_apply, Finsupp.sum, map_sum,
    smul_eq_mul, map_mul, Function.surjInv_eq, LinearMap.map_smulₛₗ, id, RingHom.id_apply]

theorem exists_dual_descent {ρ : C →ₛₗ[π] C₀} (hπ : Function.Surjective π)
    (hρ : Function.Surjective ρ) (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (x : Dual R C) : ∃ y : Dual R₀ C₀, ∀ c, y (ρ c) = π (x c) := by
  have hI : RingHom.ker π • (⊤ : Submodule R C) ≤ Submodule.comap x (RingHom.ker π) := by
    rw [Submodule.smul_le]
    intro r hr n _
    rw [Submodule.mem_comap, map_smul, smul_eq_mul]
    exact Ideal.mul_mem_right _ _ hr
  have hx : ∀ a b, ρ a = ρ b → π (x a) = π (x b) := by
    intro a b hab
    have h1 : a - b ∈ RingHom.ker π • (⊤ : Submodule R C) := (hker _).mp (by rw [map_sub, hab, sub_self])
    have h2 := hI h1
    rw [Submodule.mem_comap, map_sub] at h2
    rw [← sub_eq_zero, ← map_sub]
    exact (RingHom.mem_ker).mp h2
  let g := Function.surjInv hρ
  have hg : ∀ v, ρ (g v) = v := Function.surjInv_eq hρ
  refine ⟨{ toFun := fun v => π (x (g v)), map_add' := ?_, map_smul' := ?_ }, fun c => hx _ _ (hg _)⟩
  · intro a b
    rw [show π (x (g a)) + π (x (g b)) = π (x (g a + g b)) by simp]
    exact hx _ _ (by rw [map_add (f := _), hg, hg, hg])
  · intro r v
    obtain ⟨r', rfl⟩ := hπ r
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [← map_mul, ← smul_eq_mul, ← map_smul]
    exact hx _ _ (by rw [LinearMap.map_smulₛₗ, hg, hg])

end GlobalTheory.DualSummand

namespace GlobalTheory.DualSummand

open Module _root_.Submodule

variable {R : Type} [CommRing R] {C : Type*} [AddCommGroup C] [Module R C]
variable {R₀ : Type} [CommRing R₀] {π : R →+* R₀} {C₀ : Type*} [AddCommGroup C₀] [Module R₀ C₀]

theorem eq_zero_of_forall_dual_reduction [Projective R C] {ρ : C →ₛₗ[π] C₀}
    (hπ : Function.Surjective π) (hρ : Function.Surjective ρ)
    (hker : ∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C))
    (v : C₀) (hv : ∀ φ : Dual R₀ C₀, φ v = 0) : v = 0 := by
  obtain ⟨c, rfl⟩ := hρ v
  rw [hker]
  refine mem_smul_top_of_forall_dual _ c fun x => ?_
  obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker x
  rw [RingHom.mem_ker, ← hy]
  exact hv y

theorem exists_eq_dualAnnihilator [Projective R C] [Module.Finite R C]
    {G H : Submodule R (Dual R C)} (hGH : IsCompl G H) :
    ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  have hsurj : ∀ ψ : Dual R (Dual R C), ∃ k : C, ∀ φ : Dual R C, φ k = ψ φ := by
    intro ψ
    obtain ⟨k, hk⟩ := (Module.bijective_dual_eval R C).2 ψ
    exact ⟨k, fun φ => by rw [← hk, Dual.eval_apply]⟩
  have hsplit : ∀ φ : Dual R C, G.projection H hGH φ + H.projection G hGH.symm φ = φ :=
    projection_add_projection_eq_self hGH
  have hKL : IsCompl G.dualCoannihilator H.dualCoannihilator := by
    constructor
    · rw [disjoint_iff, eq_bot_iff]
      intro c hc
      rw [mem_inf, mem_dualCoannihilator, mem_dualCoannihilator] at hc
      rw [mem_bot, ← forall_dual_apply_eq_zero_iff R]
      intro φ
      rw [← hsplit φ, LinearMap.add_apply, hc.1 _ (projection_apply_mem hGH φ),
        hc.2 _ (projection_apply_mem hGH.symm φ), add_zero]
    · rw [codisjoint_iff, eq_top_iff]
      intro c _
      obtain ⟨k, hk⟩ := hsurj (Dual.eval R C c ∘ₗ H.projection G hGH.symm)
      obtain ⟨l, hl⟩ := hsurj (Dual.eval R C c ∘ₗ G.projection H hGH)
      refine Submodule.mem_sup.mpr ⟨k, ?_, l, ?_, ?_⟩
      · rw [mem_dualCoannihilator]
        intro g hg
        rw [hk g]
        simp [projection_apply_of_mem_right hGH.symm hg]
      · rw [mem_dualCoannihilator]
        intro h hh
        rw [hl h]
        simp [projection_apply_of_mem_right hGH hh]
      · rw [← sub_eq_zero, ← forall_dual_apply_eq_zero_iff R]
        intro φ
        rw [map_sub, map_add (f := _), hk φ, hl φ]
        simp only [LinearMap.comp_apply, Dual.eval_apply]
        rw [← LinearMap.add_apply, add_comm, hsplit φ, sub_self]
  refine ⟨G.dualCoannihilator, ⟨_, hKL⟩, le_antisymm ?_ ?_⟩
  · intro g hg
    rw [mem_dualAnnihilator]
    intro k hk
    exact (mem_dualCoannihilator _).mp hk g hg
  · intro φ hφ
    rw [mem_dualAnnihilator] at hφ
    have h0 : H.projection G hGH.symm φ = 0 := by
      ext c
      obtain ⟨k, hk, l, hl, rfl⟩ := Submodule.mem_sup.mp (hKL.sup_eq_top ▸ mem_top : c ∈ _)
      have e : H.projection G hGH.symm φ = φ - G.projection H hGH φ := by
        rw [eq_sub_iff_add_eq, add_comm, hsplit φ]
      rw [map_add (f := _), (mem_dualCoannihilator _).mp hl _ (projection_apply_mem hGH.symm φ), e,
        LinearMap.sub_apply, hφ k hk, (mem_dualCoannihilator _).mp hk _ (projection_apply_mem hGH φ)]
      simp
    rw [← hsplit φ, h0, add_zero]
    exact projection_apply_mem hGH φ

end GlobalTheory.DualSummand

namespace GlobalTheory.LiftSys

open Module _root_.Submodule GlobalTheory.DualSummand

theorem summand_dual_reduction :
    ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → ∀ (C C₀ : Type 1) [AddCommGroup C] [Module R C] [AddCommGroup C₀] [Module R₀ C₀], Module.Finite R C → Module.Projective R C → ∀ ρ : C →ₛₗ[π] C₀, Function.Surjective ρ → (∀ c, ρ c = 0 ↔ c ∈ RingHom.ker π • (⊤ : Submodule R C)) → ∀ F₀ : Submodule R₀ C₀, (∃ N₀, IsCompl F₀ N₀) → (∀ K : Submodule R C, (∃ N, IsCompl K N) → (∃ N, IsCompl K.dualAnnihilator N) ∧ K.dualAnnihilator.dualCoannihilator = K ∧ ((∀ c, c ∈ K ⊔ RingHom.ker π • ⊤ ↔ ρ c ∈ F₀) ↔ ∀ y : Module.Dual R₀ C₀, y ∈ F₀.dualAnnihilator ↔ ∃ x ∈ K.dualAnnihilator, ∀ c, y (ρ c) = π (x c))) ∧ ∀ G : Submodule R (Module.Dual R C), (∃ N, IsCompl G N) → ∃ K : Submodule R C, (∃ N, IsCompl K N) ∧ G = K.dualAnnihilator := by
  intro R R₀ _ _ π hπ C C₀ _ _ _ _ _ _ ρ hρ hker F₀ ⟨N₀, hF⟩
  refine ⟨fun K ⟨N, hKN⟩ => ⟨⟨_, isCompl_dualAnnihilator hKN⟩,
    dualAnnihilator_dualCoannihilator_eq hKN, ?_⟩, fun G ⟨H, hGH⟩ => exists_eq_dualAnnihilator hGH⟩
  have hsplit : ∀ c, K.projection N hKN c + N.projection K hKN.symm c = c :=
    projection_add_projection_eq_self hKN
  have hNK : ∀ k ∈ K, N.projection K hKN.symm k = 0 := fun k hk =>
    projection_apply_of_mem_right hKN.symm hk
  constructor
  · intro hL y
    constructor
    · intro hy
      rw [mem_dualAnnihilator] at hy
      obtain ⟨x₀, hx₀⟩ := exists_dual_lift hπ ρ y
      refine ⟨x₀ ∘ₗ N.projection K hKN.symm, ?_, fun c => ?_⟩
      · rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk]
      · rw [LinearMap.comp_apply, hx₀]
        conv_lhs => rw [← hsplit c]
        rw [map_add (f := _), map_add (f := _),
          hy _ ((hL _).mp (mem_sup_left (projection_apply_mem hKN c))), zero_add]
    · rintro ⟨x, hx, hxy⟩
      rw [mem_dualAnnihilator] at hx ⊢
      intro f hf
      obtain ⟨c, rfl⟩ := hρ f
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp ((hL c).mpr hf)
      rw [map_add (f := _), (hker m).mpr hm, add_zero, hxy, hx k hk, map_zero]
  · intro hR c
    constructor
    · intro hc
      obtain ⟨k, hk, m, hm, rfl⟩ := Submodule.mem_sup.mp hc
      rw [map_add (f := _), (hker m).mpr hm, add_zero]
      have hv : N₀.projection F₀ hF.symm (ρ k) = 0 := by
        refine eq_zero_of_forall_dual_reduction hπ hρ hker _ fun φ => ?_
        obtain ⟨x, hx, hxy⟩ := (hR (φ ∘ₗ N₀.projection F₀ hF.symm)).mp (by
          rw [mem_dualAnnihilator]
          intro f hf
          simp [projection_apply_of_mem_right hF.symm hf])
        have := hxy k
        rw [LinearMap.comp_apply] at this
        rw [this, (mem_dualAnnihilator _).mp hx k hk, map_zero]
      rw [← projection_add_projection_eq_self hF (ρ k), hv, add_zero]
      exact projection_apply_mem hF _
    · intro hc
      rw [← hsplit c]
      refine add_mem_sup (projection_apply_mem hKN c) ?_
      refine mem_smul_top_of_forall_dual _ _ fun x₀ => ?_
      obtain ⟨y, hy⟩ := exists_dual_descent hπ hρ hker (x₀ ∘ₗ N.projection K hKN.symm)
      have hyF : y ∈ F₀.dualAnnihilator := (hR y).mpr ⟨x₀ ∘ₗ N.projection K hKN.symm, by
        rw [mem_dualAnnihilator]
        intro k hk
        simp [hNK k hk], hy⟩
      rw [RingHom.mem_ker, ← LinearMap.comp_apply, ← hy]
      exact (mem_dualAnnihilator _).mp hyF _ hc

end GlobalTheory.LiftSys
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLineBundlePullbackGrpPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.SymGrpPull

theorem inv_left_comp {S T : Scheme.{0}} (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S)
    (α : B.left ⟶ A.left) (h : IsGrpPullback B A y α) :
    (GrpObj.inv : B ⟶ B).left ≫ α = α ≫ (GrpObj.inv : A ⟶ A).left := by
  have hw : α ≫ A.hom = B.hom ≫ y := h.1.w
  let f : (B ⟶ B) → (Over.mk (B.hom ≫ y) ⟶ A) := fun x =>
    Over.homMk (x.left ≫ α) (by
      change (x.left ≫ α) ≫ A.hom = B.hom ≫ y
      rw [Category.assoc, hw, ← Category.assoc, Over.w x])
  have hmul : ∀ x z : B ⟶ B, f (x * z) = f x * f z := fun x z =>
    Over.OverMorphism.ext (h.2 B x z (f x) (f z) rfl rfl).symm
  have h1 : f 1 = 1 := by
    have e : f 1 * f 1 = f 1 * 1 := by rw [← hmul, _root_.mul_one, _root_.mul_one]
    exact mul_left_cancel e
  have hinv : f (𝟙 B)⁻¹ = (f (𝟙 B))⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hmul, _root_.inv_mul_cancel, h1]
  have e := congrArg CommaMorphism.left hinv
  have e' : ((𝟙 B ≫ GrpObj.inv : B ⟶ B)).left ≫ α = (f (𝟙 B) ≫ GrpObj.inv).left := e
  simpa [f] using e'

theorem symm_pull : ∀ (S T : Scheme.{0}) (A : Over S) [GrpObj A] (B : Over T) [GrpObj B] (y : T ⟶ S) (α : B.left ⟶ A.left), IsGrpPullback B A y α → ∀ L : LB A.left, L.IsLB → LBIso (L.pull (GrpObj.inv : A ⟶ A).left) L → LBIso ((L.pull α).pull (GrpObj.inv : B ⟶ B).left) (L.pull α) := by
  intro S T A _ B _ y α h L hL hs
  have e := inv_left_comp A B y α h
  have h1 := GenSpread.lbIso_pull_pull hL (a := α) (GrpObj.inv : B ⟶ B).left rfl
  have h2 := GenSpread.lbIso_pull_pull hL (a := (GrpObj.inv : A ⟶ A).left) α e
  have h3 := GenSpread.lbIso_pullback hs α
  exact LBIso.trans (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) (pull_isLB hL _) (LBIso.symm h1)
    (LBIso.trans (pull_isLB hL _) (pull_isLB (pull_isLB hL _) _) (pull_isLB hL _) h2 h3)

end GlobalTheory.SymGrpPull
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricTwoCocycleFreeAbelianIsCoboundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoboundaryRoots

@[ext] structure CocExt (X A : Type) where
  fst : X
  snd : A

variable {X : Type} [AddCommGroup X] {A : Type} [CommGroup A]

theorem coc_zero_left (f : X → X → A)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) (c : X) : f 0 c = f 0 0 := by
  have h := hc 0 0 c
  simp only [add_zero, zero_add] at h
  exact (mul_left_cancel h).symm

theorem mul_mul_mul_inv_inv' (x y z : A) : x * y * z * x⁻¹ * y⁻¹ = z := by
  calc x * y * z * x⁻¹ * y⁻¹ = z * (x * x⁻¹) * (y * y⁻¹) := by ac_rfl
    _ = z := by simp

def extGroup (f : X → X → A) (hs : ∀ a b, f a b = f b a)
    (hc : ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) : AddCommGroup (CocExt X A) :=
  letI : Add (CocExt X A) := ⟨fun p q => ⟨p.fst + q.fst, p.snd * q.snd * f p.fst q.fst⟩⟩
  letI : Zero (CocExt X A) := ⟨⟨0, (f 0 0)⁻¹⟩⟩
  letI : Neg (CocExt X A) := ⟨fun p => ⟨-p.fst, (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹⟩⟩
  { add_assoc := fun p q r => by
        refine CocExt.ext (add_assoc p.fst q.fst r.fst) ?_
        show p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
          = p.snd * (q.snd * r.snd * f q.fst r.fst) * f p.fst (q.fst + r.fst)
        calc p.snd * q.snd * f p.fst q.fst * r.snd * f (p.fst + q.fst) r.fst
            = p.snd * q.snd * r.snd * (f (p.fst + q.fst) r.fst * f p.fst q.fst) := by ac_rfl
          _ = p.snd * q.snd * r.snd * (f p.fst (q.fst + r.fst) * f q.fst r.fst) := by rw [hc]
          _ = _ := by ac_rfl
    zero_add := fun p => by
        refine CocExt.ext (zero_add p.fst) ?_
        show (f 0 0)⁻¹ * p.snd * f 0 p.fst = p.snd
        rw [coc_zero_left f hc p.fst, mul_comm (f 0 0)⁻¹ p.snd, inv_mul_cancel_right]
    add_zero := fun p => by
        refine CocExt.ext (add_zero p.fst) ?_
        show p.snd * (f 0 0)⁻¹ * f p.fst 0 = p.snd
        rw [hs p.fst 0, coc_zero_left f hc p.fst, inv_mul_cancel_right]
    nsmul := nsmulRec
    zsmul := zsmulRec
    neg_add_cancel := fun p => by
        refine CocExt.ext (neg_add_cancel p.fst) ?_
        show (p.snd * f p.fst (-p.fst) * f 0 0)⁻¹ * p.snd * f (-p.fst) p.fst = (f 0 0)⁻¹
        rw [hs (-p.fst) p.fst]; group
    add_comm := fun p q => by
        refine CocExt.ext (add_comm p.fst q.fst) ?_
        show p.snd * q.snd * f p.fst q.fst = q.snd * p.snd * f q.fst p.fst
        rw [hs, mul_comm p.snd q.snd] }

end GlobalTheory.CoboundaryRoots

namespace GlobalTheory

theorem symm_cocycle_isCoboundary : ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (A : Type) [CommGroup A] (f : X → X → A), (∀ a b, f a b = f b a) → (∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c) → ∃ g : X → A, ∀ a b, f a b = g (a + b) * (g a)⁻¹ * (g b)⁻¹ := by
  intro X _ _ A _ f hs hc
  letI : AddCommGroup (GlobalTheory.CoboundaryRoots.CocExt X A) := GlobalTheory.CoboundaryRoots.extGroup f hs hc
  let bs := Module.Free.chooseBasis ℤ X
  let s : X →ₗ[ℤ] GlobalTheory.CoboundaryRoots.CocExt X A := bs.constr ℤ (fun i => ⟨bs i, 1⟩)
  let π : GlobalTheory.CoboundaryRoots.CocExt X A →+ X :=
    { toFun := GlobalTheory.CoboundaryRoots.CocExt.fst, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hcomp : π.toIntLinearMap.comp s = LinearMap.id :=
    bs.ext (fun i => by
      show π (s (bs i)) = bs i
      rw [show s (bs i) = ⟨bs i, 1⟩ from bs.constr_basis ℤ _ i]
      rfl)
  have hπ : ∀ x, (s x).fst = x := fun x => LinearMap.congr_fun hcomp x
  refine ⟨fun x => (s x).snd, fun a b => ?_⟩
  have h : (s (a + b)).snd = (s a).snd * (s b).snd * f (s a).fst (s b).fst :=
    congrArg GlobalTheory.CoboundaryRoots.CocExt.snd (s.map_add a b)
  rw [hπ, hπ] at h
  show f a b = (s (a + b)).snd * ((s a).snd)⁻¹ * ((s b).snd)⁻¹
  rw [h, GlobalTheory.CoboundaryRoots.mul_mul_mul_inv_inv']

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetrySecondDifferenceEqCubicalRatio
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg.SymCube

open GlobalTheory.UU

theorem sym_cube (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Spec (CommRingCat.of R)))
    (x y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (hJ : Good D.P.L z J) :
    val D.sym (x * y).left z J * cubV D.cub z J y y⁻¹ x⁻¹ =
      val D.sym x.left z J * val D.sym y.left z J * cubV D.cub z J x x⁻¹ y := by
  let G := D.P.A
  let a := x3 G 0
  let b := x3 G 1
  let sy := fun p : G3 G ⟶ G => LB.pullGen D.P.L _ _ D.sym p.left
  let cu := fun p q r : G3 G ⟶ G => LB.pullGen D.P.L (thφ G (x3 G)) thε D.cub.t (lift p (lift q r)).left
  have gs : ∀ p, (sy p).IsGen := fun p => DVR.pullGen_isGen _ _ _ _ D.sym_gen _
  have gc : ∀ p q r, (cu p q r).IsGen := fun p q r => DVR.pullGen_isGen _ _ _ _ D.cub.isGen _
  have vs : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J → ∀ p,
      val (sy p) σ.left z J = val D.sym (σ ≫ p).left z J := fun σ z J hJ p => val_pull hJ _ _ _
  let t₁ := LB.mulGen D.P.L _ _ _ _ (sy (a * b)) (cu b b⁻¹ a⁻¹)
  let t₂ := LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ (sy a) (sy b)) (cu a a⁻¹ b)
  have ev : ∀ {T' : Over (Spec (CommRingCat.of R))} (σ : T' ⟶ G3 G) {z : T'.left} {J}, Good D.P.L z J →
      val t₁ σ.left z J = val D.sym ((σ ≫ a) * (σ ≫ b)).left z J * cubV D.cub z J (σ ≫ b) (σ ≫ b)⁻¹ (σ ≫ a)⁻¹ ∧
      val t₂ σ.left z J = val D.sym (σ ≫ a).left z J * val D.sym (σ ≫ b).left z J *
        cubV D.cub z J (σ ≫ a) (σ ≫ a)⁻¹ (σ ≫ b) := fun σ z J hJ => by
    constructor
    · rw [← MonObj.comp_mul, ← GrpObj.comp_inv, ← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs σ hJ _) (val_cub D.cub σ hJ _ _ _))
    · rw [← GrpObj.comp_inv]
      exact (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs σ hJ _) (vs σ hJ _))) (val_cub D.cub σ hJ _ _ _))
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
  have e₀ : e ≫ a = 1 := by simp [e, a, x3]
  have e₁ : e ≫ b = 1 := by simp [e, b, x3]
  let ρ : T ⟶ G3 G := lift x (lift y 1)
  have r₀ : ρ ≫ a = x := by simp [ρ, a, x3]
  have r₁ : ρ ≫ b = y := by simp [ρ, b, x3]
  have h3 := GlobalTheory.UU.surjective_cube GlobalTheory.globalFns_holds D.P.isAb
  have key : val t₁ ρ.left z J = val t₂ ρ.left z J := by
    refine gen_unique' D.P.isLB (fun V _ k => ?_) (G3 G).hom e.left (Over.w e) h3
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gc _ _ _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (gs _) (gs _)) (gc _ _ _))
      (fun y I hI => ?_) _ ρ.left z J hJ
    · refine (DVR.prod_sum₂ (K := Fin 2 ⊕ Fin 2) (K' := thK) (U := V) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := Fin 2) (U := V) _ (prod_sym a k) (prod_sym b k))
        (prod_cub a a⁻¹ b k)).trans (Eq.trans ?_
        (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _ (prod_sym (a * b) k) (prod_cub b b⁻¹ a⁻¹ k)).symm)
      have m₁ : b * b⁻¹ * a⁻¹ = a⁻¹ := by rw [mul_inv_cancel, _root_.one_mul]
      have m₂ : b * b⁻¹ = 1 := mul_inv_cancel b
      have m₃ : b * a⁻¹ = a⁻¹ * b := mul_comm _ _
      have m₄ : b⁻¹ * a⁻¹ = (a * b)⁻¹ := (mul_inv_rev a b).symm
      have m₅ : a * a⁻¹ * b = b := by rw [mul_inv_cancel, _root_.one_mul]
      have m₆ : a * a⁻¹ = 1 := mul_inv_cancel a
      rw [m₁, m₂, m₃, m₄, m₅, m₆]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    · have s1 : val D.sym (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G).left y I = 1 := by
        rw [one_left]
        exact (val_pull hI D.sym (eSec G) _).symm.trans ((val_corr hI D.sym_rig _).trans (val_one _))
      refine (ev e hI).1.trans (Eq.trans ?_ (ev e hI).2.symm)
      rw [e₀, e₁]
      simp only [inv_one, _root_.mul_one, s1, _root_.one_mul]
  have := (ev ρ hJ).1.symm.trans (key.trans (ev ρ hJ).2)
  rwa [r₀, r₁] at this

end GlobalTheory.PolDeg.SymCube
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TheoremOfSquareCechPicardTranslates
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSym

theorem lam_mul_left {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] (hA : IsAbelianScheme A)
    (c : Pic A.left) {Y : Over S} (a a' x : Y ⟶ A) : lam c (a * a') x = lam c a x + lam c a' x := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  have hP : (abelian₂ A L).IsLB := LB.isLB_linComb hL _ _
  have e : ∀ (Y : Over S) (a b : Y ⟶ A), evc hP a b = lam (cls L hL) a b := fun Y a b ↦ by
    rw [evc, show cls _ hP = lam (cls L hL) (fst A A) (snd A A) from cls_cube_two hL _ _ hP, pull_lam, lift_fst,
      lift_snd]
  have h := GlobalTheory.CubeNoeth.isAdditive_of_triv_axes hA hA hP
    (by rw [triv_ev_iff hP, e, lam_one_left]) (by rw [triv_ev_iff hP, e, lam_one_right])
  simpa only [e] using (isAdditive_iff hP).1 h Y a a' x

theorem pull_mul_add_pull_mul_inv : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A], IsAbelianScheme A → ∀ (c : Pic A.left) (Y : Over S) (x a : Y ⟶ A), GlobalTheory.CechPic.pull (x * a).left c + GlobalTheory.CechPic.pull (x * a⁻¹).left c = 2 • GlobalTheory.CechPic.pull (x).left c + GlobalTheory.CechPic.pull (a).left c + GlobalTheory.CechPic.pull (a⁻¹).left c - 2 • GlobalTheory.CechPic.pull ((1 : Y ⟶ A)).left c := by
  intro S _ A _ hA c Y x a
  haveI := hA.comm
  have h := lam_mul_left hA c a a⁻¹ x
  rw [mul_inv_cancel, lam_one_left, lam_comm c a x, lam_comm c a⁻¹ x, lam, lam] at h
  rw [← sub_eq_zero, h]
  abel

end GlobalTheory.SquareSym
end

