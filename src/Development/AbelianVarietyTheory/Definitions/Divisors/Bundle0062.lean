module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsGDatumOneOneOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2015
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1921
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0532
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsToricRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsGHeckeMapForget
section
noncomputable section

namespace GlobalTheory.UPel.HT.Gen

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R₁ R₂ : Type} [CommRing R₁] [CommRing R₂] [Algebra ℚ R₁] [Algebra ℚ R₂]
  {S S' : Scheme.{0}}

def IsGGPull {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
    (o' : GObj gb₂ N s') (o : GObj gb₁ N s) (f : S' ⟶ S) : Prop :=
  ∃ (φA : o'.A.left ⟶ o.A.left) (φ₂ : (G2 o'.A).left ⟶ (G2 o.A).left),
    IsGrpPullback o'.A o.A f φA ∧ IsSquare φA φ₂ ∧
    (∀ c : G.O, (o'.act.act c).left ≫ φA = φA ≫ (o.act.act c).left) ∧ Nonempty (LBIso o'.P (o.P.pull φ₂)) ∧
    ∀ y : G.La, (o'.eta y).left ≫ φA = f ≫ (o.eta y).left

def GBase.IsMap (β : R₁ →+* R₂) (gb₁ : GBase G R₁) (gb₂ : GBase G R₂) : Prop :=
  gb₂.ρ = β gb₁.ρ ∧ ∀ i, gb₂.t i = β.comp (gb₁.t i)

def GBase.map (β : R₁ →+* R₂) (gb : GBase G R₁) : GBase G R₂ where
  ρ := β gb.ρ
  ρ_root := by simpa using congrArg β gb.ρ_root
  t i := β.comp (gb.t i)
  t_ω i := by rw [RingHom.comp_apply, gb.t_ω]
  comax i j hij := by
    have h := congrArg (Ideal.map β) (gb.comax i j hij)
    rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
    simpa [Function.comp_def] using h

theorem GBase.IsMap.id (gb : GBase G R₁) : GBase.IsMap (RingHom.id R₁) gb gb :=
  ⟨rfl, fun _ => rfl⟩

def IsGGPullOver (β : R₁ →+* R₂) {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
    (o' : GObj gb₂ N s') (o : GObj gb₁ N s) (f : S' ⟶ S) : Prop :=
  f ≫ s = s' ≫ spMap β ∧ GBase.IsMap β gb₁ gb₂ ∧ IsGGPull o' o f

section Over

variable {β : R₁ →+* R₂} {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {N : ℕ} {s' : S' ⟶ Sp R₂} {s : S ⟶ Sp R₁}
  {o' : GObj gb₂ N s'} {o : GObj gb₁ N s} {f : S' ⟶ S}

end Over

variable {R : Type} [CommRing R] [Algebra ℚ R]

theorem isGGPull_iff {gb : GBase G R} {N : ℕ} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj gb N s'}
    {o : GObj gb N s} {f : S' ⟶ S} : IsGGPull o' o f ↔ Nonempty (GObjMap o' o f) :=
  ⟨fun ⟨φ, φ₂, h₁, h₂, h₃, ⟨h₄⟩, h₅⟩ => ⟨⟨φ, φ₂, h₁, h₂, h₃, h₄, h₅⟩⟩,
    fun ⟨m⟩ => ⟨m.φ, m.φ₂, m.cart, m.sq, m.act, ⟨m.pol⟩, m.eta⟩⟩

theorem isGGPullOver_id_iff {gb : GBase G R} {N : ℕ} {s' : S' ⟶ Sp R} {s : S ⟶ Sp R} {o' : GObj gb N s'}
    {o : GObj gb N s} {f : S' ⟶ S} :
    IsGGPullOver (RingHom.id R) o' o f ↔ f ≫ s = s' ∧ Nonempty (GObjMap o' o f) := by
  have e : spMap (RingHom.id R) = 𝟙 (Sp R) := Spec.map_id (CommRingCat.of R)
  rw [IsGGPullOver, e, Category.comp_id, isGGPull_iff]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, GBase.IsMap.id gb, h.2⟩⟩

theorem IsGGPull.refl {gb : GBase G R} {N : ℕ} {s : S ⟶ Sp R} (o : GObj gb N s) : IsGGPull o o (𝟙 S) :=
  isGGPull_iff.2 (Unique.gObjMap_id o)

section Comp

variable {R₃ : Type} [CommRing R₃] [Algebra ℚ R₃] {gb₁ : GBase G R₁} {gb₂ : GBase G R₂} {gb₃ : GBase G R₃} {N : ℕ}
  {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R₁} {s₂ : S₂ ⟶ Sp R₂} {s₃ : S₃ ⟶ Sp R₃} {o₁ : GObj gb₁ N s₁}
  {o₂ : GObj gb₂ N s₂} {o₃ : GObj gb₃ N s₃} {f : S₃ ⟶ S₂} {f' : S₂ ⟶ S₁}

end Comp

theorem GObj.eta_zero {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) : o.eta 0 = 1 := by
  have h := o.eta_add 0 0
  rw [add_zero] at h
  exact mul_left_cancel (a := o.eta 0) (by rw [_root_.mul_one]; exact h.symm)

theorem GObj.eta_neg {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (x : G.La) :
    o.eta (-x) = (o.eta x)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  rw [← o.eta_add, add_neg_cancel, GObj.eta_zero]

theorem GObj.eta_nsmul {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (n : ℕ) (x : G.La) :
    o.eta (n • x) = o.eta x ^ n := by
  induction n with
  | zero => rw [zero_nsmul, pow_zero, GObj.eta_zero]
  | succ n ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]

def gHeckeSub {gb : GBase G R} {M : ℕ} {s : S ⟶ Sp R} (o : GObj gb M s) (g : G.La →ₗ[G.O] G.La) (N : ℕ) :
    Subgroup (𝟙_ (Over S) ⟶ o.A) where
  carrier := {h | ∃ x, h = o.eta (N • g x)}
  one_mem' := ⟨0, by rw [map_zero, smul_zero, GObj.eta_zero]⟩
  mul_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, by rw [map_add (f := _), smul_add, o.eta_add]⟩
  inv_mem' := by
    rintro _ ⟨x, rfl⟩
    exact ⟨-x, by rw [map_neg, smul_neg, GObj.eta_neg]⟩

def IsGHecke {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) {s : S ⟶ Sp R} (o : GObj gb (N * k) s)
    (o' : GObj gb N s) (ψ : o.A ⟶ o'.A) : Prop :=
  IsMonHom ψ ∧ (∀ c' : G.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta (g x) ≫ ψ) ∧
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left ∧
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) ∧ c ∣ k ^ 2

def IsGHeckeMap {gb : GBase G R} (g : G.La →ₗ[G.O] G.La) (c k N : ℕ) (X : GenModel gb N) (X' : GenModel gb (N * k))
    (π : X'.X ⟶ X.X) : Prop :=
  π ≫ X.s = X'.s ∧ ∃ (o' : GObj gb N X'.s) (ψ : X'.univ.A ⟶ o'.A), IsGHecke g c k N X'.univ o' ψ ∧
    Nonempty (GObjMap o' X.univ π)

section API

variable {gb : GBase G R} {g : G.La →ₗ[G.O] G.La} {c k N : ℕ} {s : S ⟶ Sp R} {o : GObj gb (N * k) s}
  {o' : GObj gb N s} {ψ : o.A ⟶ o'.A}

theorem IsGHecke.isMonHom (h : IsGHecke g c k N o o' ψ) : IsMonHom ψ := h.1

theorem IsGHecke.act (h : IsGHecke g c k N o o' ψ) (c' : G.O) : o.act.act c' ≫ ψ = ψ ≫ o'.act.act c' := h.2.1 c'

theorem IsGHecke.eta (h : IsGHecke g c k N o o' ψ) (x : G.La) : o'.eta x = o.eta (g x) ≫ ψ := h.2.2.1 x

theorem IsGHecke.cover (h : IsGHecke g c k N o o' ψ) :
    GlobalTheory.ZM.IsGaloisCover (gHeckeSub o g N) (fun h => (Hecke.transl h.1).left) ψ.left := h.2.2.2.1

theorem IsGHecke.pol (h : IsGHecke g c k N o o' ψ) :
    Nonempty (LBIso (Hecke.lbPow o.P (k ^ 2 / c)) (o'.P.pull (Hecke.sq2 ψ))) := h.2.2.2.2.1

variable {X : GenModel gb N} {X' : GenModel gb (N * k)} {π : X'.X ⟶ X.X}

end API

def GObj.forgetMul {gb : GBase G R} {N k : ℕ} (hN : 0 < N) (hk : 0 < k) {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    GObj gb N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  rosati := o.rosati
  lie := o.lie
  lieRank := o.lieRank
  eta x := o.eta (k • x)
  eta_add x y := by rw [smul_add, o.eta_add]
  eta_lin c x := by rw [smul_comm, o.eta_lin]
  eta_ker x := by rw [smul_comm, smul_smul, o.eta_ker]
  geom K _ _ x β hx := by
    obtain ⟨I, hI⟩ := o.geom K x β hx
    refine ⟨I, fun y => ?_⟩
    rw [o.eta_nsmul, MonObj.comp_pow, hI, I.tower N k hN hk]

theorem gHeckeSub_smul_id_eq_one {gb : GBase G R} {N k : ℕ} {s : S ⟶ Sp R} (o : GObj gb (N * k) s) :
    ∀ h ∈ gHeckeSub o (k • LinearMap.id) N, h = 1 := by
  rintro _ ⟨x, rfl⟩
  rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul]
  exact o.eta_ker x

end GlobalTheory.UPel.HT.Gen
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsLogMult
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic

namespace GlobalTheory.Discrepancy

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

abbrev fnPull (s : Y ⟶ X) [IsDominant s] : X.functionFieldˣ →* Y.functionFieldˣ :=
  Units.map (functionFieldMap s).toMonoidHom

def pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) : CartierDiv Y :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose

theorem isEqn_pullCart (s : Y ⟶ X) [IsDominant s] {D : CartierDiv X} {y : Y} {g : X.functionFieldˣ}
    (h : D.IsEqn (s y) g) : (pullCart s D).IsEqn y (fnPull s g) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.2 y g h

theorem toPic_pullCart (s : Y ⟶ X) [IsDominant s] (D : CartierDiv X) :
    toPic (pullCart s D) = CechPic.pull s (toPic D) :=
  (GlobalTheory.Cartier.exists_pullback_cartierDiv X Y s D).choose_spec.1

theorem pullCart_add (s : Y ⟶ X) [IsDominant s] (D E : CartierDiv X) :
    pullCart s (D + E) = pullCart s D + pullCart s E :=
  CartierDiv.ext_of_isEqn fun y =>
    have ⟨g, hg⟩ := D.exists_isEqn (s y)
    have ⟨g', hg'⟩ := E.exists_isEqn (s y)
    ⟨_, isEqn_pullCart s (hg.add hg'),
      (map_mul (fnPull s) g g').symm ▸ (isEqn_pullCart s hg).add (isEqn_pullCart s hg')⟩

def pullCartHom (s : Y ⟶ X) [IsDominant s] : CartierDiv X →+ CartierDiv Y :=
  AddMonoidHom.mk' (pullCart s) (pullCart_add s)

variable {k : Type} [Field k]

def DivOver.Over {p : X ⟶ Sp k} (s : Y ⟶ X) [IsDominant s] (E' : DivOver (s ≫ p)) (E : DivOver p) :
    Prop :=
  ∀ f, f ∈ E.ring ↔ functionFieldMap s f ∈ E'.ring

structure IsLogRes (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (s : Y ⟶ X) [IsDominant s] (K : CartierDiv Y) (B : Closeds Y) : Prop where

  smooth : SmoothOfRelativeDimension n (s ≫ p)

  proj : IsProjOver (s ≫ p)

  bir : Function.Bijective (functionFieldMap s)

  div : IsDivOfForm K (EtaleKlt.ratPull p s n η)

  snc : FinalTheorems.Snc (Scheme.IdealSheafData.vanishingIdeal B)

  supp : (pullCart s G - m • K).supp ≤ B

structure IsLogMult (p : X ⟶ Sp k) (n : ℕ) (Δ : X → ℚ) (η : RatForms p n) (m : ℕ)
    (G : CartierDiv X) : Prop where

  ne_zero : η ≠ 0

  pos : 0 < m

  eqn : ∀ x g, G.IsEqn x g → IsLogEqn p Δ η x m g

theorem IsLogCanonicalMultiple.exists_isLogMult {p : X ⟶ Sp k} {n : ℕ} {Δ : X → ℚ} {m : ℕ}
    {G : CartierDiv X} (h : IsLogCanonicalMultiple p n Δ m G) (hm : 0 < m) :
    ∃ η, IsLogMult p n Δ η m G :=
  have ⟨η, h₁, h₂⟩ := h; ⟨η, h₁, hm, h₂⟩

def InMultAt (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X) (x : X)
    (u : X.functionFieldˣ) : Prop :=
  ∀ g, G.IsEqn x g → ∀ E : DivOver p, E.Through x → -1 < (E.ord u : ℚ) + discrep E η m g

def IsMultIdeal (p : X ⟶ Sp k) (n : ℕ) (η : RatForms p n) (m : ℕ) (G : CartierDiv X)
    (J : X.IdealSheafData) : Prop :=
  ∀ (U : X.affineOpens) (f : Γ(X, U.1)), f ∈ J.ideal U ↔
    ∀ (x : X) (hx : x ∈ U.1) (u : X.functionFieldˣ),
      (u : X.functionField) = fnOf U.1 (gen_mem hx) f → InMultAt p n η m G x u

structure IsSncChart [IsLocallyNoetherian Y] (q : Y ⟶ Sp k) (n : ℕ) (B : Closeds Y) (y : Y)
    (U : Y.Opens) (hy : y ∈ U) (z : Fin n → Γ(Y, U)) (J : Finset (Fin n)) (w : Fin n → Y)
    (u : Fin n → Y.functionFieldˣ) : Prop where

  frame : IsFrame (dOn q z)

  val : ∀ j ∈ J, (u j : Y.functionField) = fnOf U (gen_mem hy) (z j)

  spec : ∀ j ∈ J, w j ⤳ y

  coheight : ∀ j ∈ J, Order.coheight (w j) = 1

  inj : Set.InjOn w J

  ord_self : ∀ j ∈ J, Scheme.ord (u j : Y.functionField) (w j) = 1

  ord_other : ∀ j ∈ J, ∀ v, v ⤳ y → v ≠ w j → Scheme.ord (u j : Y.functionField) v = 0

  mem : ∀ v, v ⤳ y → Order.coheight v = 1 → (v ∈ B ↔ ∃ j ∈ J, v = w j)

end GlobalTheory.Discrepancy
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMinAt
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SiegJoin

open GlobalTheory.Poinc GlobalTheory.PolDeg

variable {g n : ℕ}

def BlowAt (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (φ : InvFun ℤ) (d : ℕ)
    {S : Scheme.{0}} (π : S ⟶ Z) (j : F.X ⟶ S) (BD : EffCartierData S) : Prop :=
  ∃ J : Z.IdealSheafData, 1 ≤ d ∧ (∀ x ∈ J.support, x ∉ Set.range i) ∧ ValOn F i φ J d ∧ IsNormBl π J ∧
    IsProjOver (π ≫ z) ∧ Dense (Set.range j) ∧ j ≫ π = i ∧ π ⁻¹' Set.range i = Set.range j ∧
    BD.idealSheaf = J.comap π ∧ ValOn F j φ BD.idealSheaf d

end GlobalTheory.SiegJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPoinc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H}

def UValOn (Xo : Moduli D l) (c : Coeff l) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) (φ : InvFun (𝓞 E)) (J : S.IdealSheafData)
    (d : ℕ) : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ →
    ∀ (χ : Sp W ⟶ S) (y : Sp (FractionRing W) ⟶ Xo.XF c), y ≫ j = jK W ≫ χ →
    ∀ (t : SAB H (Sp W)) (tK : SAB H (Sp (FractionRing W))), Nonempty (SABMap tK t (jK W)) →
      Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _)) → ∀ P : PELUnif (maximalIdeal W) t,
      ∀ be ∈ levelForms H 1 P.D.toPre.X, IsMonomial P.D.toPre ![ϖ] ![be] →
        ∃ n : ℕ, (n : ℝ) = d * φ.evalZ be ∧ idlAlong J χ = Ideal.span {ϖ ^ n}

def GenOf (Xo : Moduli D l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : Prop :=
  ∃ tK : SAB H (Sp (FractionRing R)), Nonempty (SABMap tK t (jK R)) ∧ Nonempty (SABMap tK Xo.univ.t (y ≫ pullback.fst _ _))

variable {Xo : Moduli D l} {c : Coeff l}

theorem exists_over_iff {R : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (y : Sp (FractionRing R) ⟶ Xo.XF c) :
    (∃ σ : Sp R ⟶ Sp c.F, jK R ≫ σ = y ≫ pullback.snd _ _) ↔ ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := by
  constructor
  · rintro ⟨σ, -⟩ n hn
    have := (IsUnit.mk0 (n : c.F) (Nat.cast_ne_zero.2 hn)).map (Spec.preimage σ).hom
    rwa [map_natCast] at this
  · intro hu
    haveI := c.fin
    let g : c.F →+* FractionRing R := (Spec.preimage (y ≫ pullback.snd _ _)).hom
    have hint : ∀ a : c.F, ∃ r : R, algebraMap R (FractionRing R) r = g a := fun a => by
      obtain ⟨m, hm, ha⟩ := ((IsFractionRing.isAlgebraic_iff ℤ ℚ c.F).2
        (Algebra.IsAlgebraic.isAlgebraic a)).exists_integral_multiple
      have hint : IsIntegral R (g (m • a)) := by
        obtain ⟨p, hp, h0⟩ := ha
        refine ⟨p.map (Int.castRingHom R), hp.map _, ?_⟩
        rw [Polynomial.eval₂_map, RingHom.ext_int ((algebraMap R (FractionRing R)).comp (Int.castRingHom R))
          (g.comp (algebraMap ℤ c.F)), ← Polynomial.hom_eval₂, h0, map_zero]
      obtain ⟨r, hr⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint
      have hum : IsUnit (m : R) := by
        have := hu m.natAbs (by simpa using hm)
        rcases Int.natAbs_eq m with e | e <;> rw [e] <;> simpa using this
      obtain ⟨u, hu'⟩ := hum
      refine ⟨(↑u⁻¹ : R) * r, ?_⟩
      have e : g (m • a) = algebraMap R (FractionRing R) u * g a := by simp [hu']
      rw [map_mul, hr, e, ← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    choose f hf using hint
    have hi := IsFractionRing.injective R (FractionRing R)
    let b : c.F →+* R :=
      { toFun := f
        map_one' := hi (by simp [hf])
        map_mul' := fun _ _ => hi (by simp [hf])
        map_zero' := hi (by simp [hf])
        map_add' := fun _ _ => hi (by simp [hf]) }
    refine ⟨spMap b, ?_⟩
    rw [← Spec.map_preimage (y ≫ pullback.snd _ _), ← Spec.map_comp]
    congr 1
    ext a
    exact hf a

end GlobalTheory.UPoinc
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.HasPolChartOf
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Act

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def IsPrim {S : Scheme.{0}} (P : PolAV S) (w : P.A ⟶ P.A) : Prop :=
  letI := P.isAb.comm
  ∃ u : LB.Gen (LB.LinComb P.L (K := Fin 4) ![(padd P.A (𝟙 _) w).left, 𝟙 P.A.left, w.left, (toUnit P.A ≫ η[P.A]).left]
    ![1, -2, -1, 2]), u.IsGen

end Act

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {o : Type} [CommRing o] {b : o →+* c.F}

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsMonomialTauOfTauIn
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep.Model

variable {V : Type} [CommRing V] [IsDomain V]

theorem isMonomialTau_of_tauIn {Q : Data V} {τ₀ : Gens Q} {N : ℕ} {s : Fin N → V}
    {ε : Fin N → LinearMap.BilinForm ℤ Q.X} (h : TauIn Q τ₀ s ε) : Q.IsMonomialTau s ε := by
  intro a b
  obtain ⟨hg, k, hk, hv⟩ := h a b
  exact ⟨k, hk, Exists.intro (τ₀ a b) ⟨hg, hv⟩⟩

end GlobalTheory.Poinc.Sep.Model
end
end

