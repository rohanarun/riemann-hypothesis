module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsUnifOfIsMumfordOf
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1962
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1917
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SelfTorusExtensionCoordValuesEqOne
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0151
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1275

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

variable {R : Type} [CommRing R] [IsDomain R] {R' : Type} [CommRing R'] [IsDomain R']

def Half (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ) : Prop :=
  letI := D.P.isAb.comm
  ∃ (β : D.P.A.left ⟶ Q.B.left) (β₂ : (G2 D.P.A).left ⟶ (G2 Q.B).left)
    (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ Q.B Q.M.L).pull β₂)),
    IsGrpPullback D.P.A Q.B (spMap ρ) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ (T : Over (Sp R')) z J J', Good Q.M.L z J → Good D.P.L z J' →
      lamVal w (lift (1 : T ⟶ D.P.A) (1 : T ⟶ D.P.A)).left z J J' = 1) ∧
    (∀ a, (D.c a).left ≫ β = spMap ρ ≫ (Q.c (e a)).left) ∧
    ∀ κ : (TK R').left ⟶ (TK R).left, κ ≫ jK R = jK R' ≫ spMap ρ → ∀ a b z J J', Good Q.M.L z J → Good D.P.L z J' →
      val (D.tau a b) (𝟙 _) z J' * gm (𝟙 (TK R').left) z ⊤ (unitOn (f a b)) =
        lamVal w (lift (toUnit (TK R') ≫ D.c a) (toUnit (TK R') ≫ D.c b)).left z J J' * val (Q.tau (e a) (e b)) κ z J

theorem Half.refines {Q : Data R} {ρ : R →+* R'} {D : DegPre R'} {e : D.X ≃+ Q.X} (h : Half Q ρ D e fun _ _ => 1) :
    Refines Q ρ D e := by
  obtain ⟨β, β₂, w, h₁, h₂, h₃, -, h₄, h₅⟩ := h
  refine ⟨β, β₂, w, h₁, h₂, h₃, h₄, fun κ hκ a b z J J' hJ hJ' => ?_⟩
  have := h₅ κ hκ a b z J J' hJ hJ'
  rwa [show unitOn (1 : (FractionRing R')ˣ) = 1 from map_one _, map_one, _root_.mul_one] at this

def rescale (D : DegPre R) (g : D.X → (FractionRing R)ˣ) : DegPre R :=
  { D with
    psi := fun χ => GlobalTheory.UU.scaleGen (unitOn (g χ)) (D.psi χ)
    psi_gen := fun χ => GlobalTheory.UU.scaleGen_isGen _ (D.psi_gen χ) }

def EvenDefect (D : DegPre R) (h : D.X → (FractionRing R)ˣ) : Prop :=
  ∀ χ z J, Good D.P.L z J →
    val (D.psi (-χ)) (𝟙 _) z J * val D.sym (D.xK χ) z J =
      gm (𝟙 (TK R).left) z ⊤ (unitOn (h χ)) * val (D.psi χ) (𝟙 _) z J

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
section
noncomputable section

namespace GlobalTheory.UPel.HT.ES

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {S : Scheme.{0}}

def uIdeal (D : Datum p) (r : ℤ) : Ideal (𝓞 D.F) := Ideal.span {(p : 𝓞 D.F), D.ω - (r : 𝓞 D.F)}

theorem p_mem_uIdeal (D : Datum p) (r : ℤ) : (p : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert _ _)

theorem sub_mem_uIdeal (D : Datum p) (r : ℤ) : D.ω - (r : 𝓞 D.F) ∈ uIdeal D r :=
  Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

def IsPIsog {N : ℕ} {s : S ⟶ Sp R} (c : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  (∃ k : ℕ, c = p ^ k) ∧
  IsMonHom ψ ∧ (∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ o'.act.act c') ∧ (∀ x, o'.eta x = o.eta x ≫ ψ) ∧
    Nonempty (LBIso (Hecke.lbPow o.P c) (o'.P.pull (sq2 ψ))) ∧
    ∃ ψ' : o'.A ⟶ o.A, IsMonHom ψ' ∧ ψ ≫ ψ' = (𝟙 o.A) ^ c ∧ ψ' ≫ ψ = (𝟙 o'.A) ^ c

theorem IsPIsog.exists_eq_pow {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : ∃ k : ℕ, c = p ^ k := h.1

theorem IsPIsog.pos {N : ℕ} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) : 0 < c := by
  obtain ⟨k, rfl⟩ := h.1
  exact pow_pos (Fact.out : p.Prime).pos k

def KilledBy {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) {T : Over S} (g : T ⟶ o.A) : Prop :=
  ∀ a ∈ v, g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1

def IsTj {N : ℕ} {s : S ⟶ Sp R} (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) : Prop :=
  ∀ (k : Type) [Field k] [IsAlgClosed k] [CharZero k] (x : Sp k ⟶ S),
    (∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
    Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)

structure TjCorr {N : ℕ} (F : RepFam b N) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) where

  Y : Scheme.{0}

  s : Y ⟶ F.X

  t : Y ⟶ F.X
  st : s ≫ F.s = t ≫ F.s

  o : Obj b N (s ≫ F.s)

  o' : Obj b N (s ≫ F.s)
  ms : ObjMap o F.univ s
  mt : ObjMap o' F.univ t

  ψ : o.A ⟶ o'.A
  isog : IsPIsog c o o' ψ
  tj : IsTj r w j o o' ψ

  wPrime : w.IsPrime

  uLe : uIdeal D r ≤ w

  pReg : ∀ (U : Y.Opens) (f : Γ(Y, U)), (p : Γ(Y, U)) * f = 0 → f = 0

  sFin : IsFinite s

  tFin : IsFinite t

  sSurj : Surjective s

theorem KilledBy.one {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (v : Ideal (𝓞 D.F)) (T : Over S) :
    KilledBy o v (1 : T ⟶ o.A) := fun a _ => by
  haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
  exact one_comp _

theorem pReg_of_flat {Y : Scheme.{0}} (s : Y ⟶ Sp R) [Flat s] (hR : ∀ a : R, (p : R) * a = 0 → a = 0)
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  refine Y.sheaf.eq_of_locally_eq' (fun V : {V : Y.affineOpens // V.1 ≤ U} => V.1.1) U
    (fun V => homOfLE V.2) ?_ f 0 fun V => ?_
  · intro y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, hV⟩, hVU⟩, hyV⟩
  · have hfl : (s.appLE ⊤ V.1.1 le_top).hom.Flat :=
      HasRingHomProperty.appLE (P := @Flat) s inferInstance ⟨⊤, isAffineOpen_top _⟩ V.1 le_top
    have hp : (p : Γ(Sp R, ⊤)) ∈ nonZeroDivisors Γ(Sp R, ⊤) := by
      rw [mem_nonZeroDivisors_iff_left]
      intro a ha
      let e := (Scheme.ΓSpecIso (CommRingCat.of R)).commRingCatIsoToRingEquiv
      refine e.injective ((hR _ ?_).trans (map_zero e).symm)
      rw [← map_natCast e, ← map_mul, ha, map_zero]
    letI := (s.appLE ⊤ V.1.1 le_top).hom.toAlgebra
    haveI : Module.Flat Γ(Sp R, ⊤) Γ(Y, V.1.1) := hfl
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Γ(Y, V.1.1)) hp
    let ρ : Γ(Y, U) →+* Γ(Y, V.1.1) := (Y.presheaf.map (homOfLE V.2).op).hom
    show ρ f = ρ 0
    refine hreg ?_
    simp only [Algebra.smul_def, map_natCast, map_zero, mul_zero]
    rw [← map_natCast ρ, ← map_mul, hf, map_zero]

theorem pReg_of_isUnit {Y : Scheme.{0}} (s : Y ⟶ Sp R) (hR : IsUnit (p : R))
    (U : Y.Opens) (f : Γ(Y, U)) (hf : (p : Γ(Y, U)) * f = 0) : f = 0 := by
  have := hR.map (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appLE ⊤ U le_top).hom)
  rw [map_natCast] at this
  exact this.mul_right_eq_zero.1 hf

def IsWOrd {N : ℕ} {s : S ⟶ Sp R} (o : Obj b N s) (w : Ideal (𝓞 D.F)) {k : Type} [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) : Prop :=
  CharP k p ∧ w.IsPrime ∧ (p : 𝓞 D.F) ∈ w ∧
    Nat.card {g : Over.mk x ⟶ o.A // KilledBy o w g} = Ideal.absNorm w ^ (D.m * (D.n - 1))

end GlobalTheory.UPel.HT.ES
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.Sep

def DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  ∃ P₀ : Sp k₀ ⟶ Y, spMap k₀.subtype ≫ P₀ = P

variable {V : Type} [CommRing V] [IsDomain V]

abbrev Gens (Q : Data V) : Type := ∀ a b : Q.X, LB.Gen (LB.LinComb Q.M.L (lamPts (Q.c a) (Q.c b)) negε)

def TauIn (Q : Data V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V) (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.M.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J

def FromBase (Q : Data V) (τ₀ : Gens Q) {W₀ : Type} [CommRing W₀] (ιb : W₀ →+* V) : Prop :=
  ∃ (B₀ : Over (Sp W₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (τ₁ : ∀ a b : Q.X, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε))
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
    (w : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback Q.B B₀ (spMap ιb) β ∧ IsSquare β β₂ ∧ w.IsGen ∧
    (∀ a, (Q.c a).left ≫ β = spMap ιb ≫ (c₀ a).left) ∧ (∀ a b, (τ₁ a b).IsGen) ∧
    ∀ (T : Over (Sp V)) (a b : Q.X) z J J', Good M₀ z J → Good Q.M.L z J' →
      val (τ₀ a b) (toUnit T).left z J' =
        lamVal w (lift (toUnit T ≫ Q.c a) (toUnit T ≫ Q.c b)).left z J J' * val (τ₁ a b) (T.hom ≫ spMap ιb) z J

def UnifOver {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (j : F.X ⟶ S) [IsLocalRing V]
    (ξ : Sp V ⟶ S) (Q : Data V) : Prop :=
  IsCN V ∧ ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : V →+* R'), IsCN R' → Function.Injective ρ →
    ρ.Finite → ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (A : PolAV (Sp (FractionRing R')))
        (_ : Unif (maximalIdeal R') D A G') (y' : Sp (FractionRing R') ⟶ F.X) (α : A.A.left ⟶ F.univ.A.left)
        (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
        IsSemiAbelian G' ∧ y' ≫ j = jK R' ≫ spMap ρ ≫ ξ ∧ IsGrpPullback A.A F.univ.A y' α ∧
          IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂)

def SepAt (Q : Data V) (τ₀ : Gens Q) {m N : ℕ} (s : Fin m ⊕ Fin N → V) {K : Type} [Field K] (ev : V →+* K)
    (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s (.inl i)) = 0) ∧
  (∀ (o' : Type) [CommRing o'] (ζ' : o') (g' n' : ℕ) (F' : SFam g' n' ζ') (lam : Sp V ⟶ F'.X) (β : Q.B.left ⟶ F'.univ.A.left)
      (β₂ : (G2 Q.B).left ⟶ (G2 F'.univ.A).left), 1 ≤ n' → DefOver k₀ (spMap ev ≫ lam ≫ F'.s) →
      IsGrpPullback Q.B F'.univ.A lam β → IsSquare β β₂ → LBIso (abelian₂ Q.B Q.M.L) (F'.univ.P.pull β₂) →
      ∀ a, DefOver k₀ (spMap ev ≫ (Q.c a).left ≫ β)) ∧
  ∀ (W₀ : Type) [CommRing W₀] (ιb : W₀ →+* V), FromBase Q τ₀ ιb → (∀ a, ev (ιb a) ∈ k₀) → ∀ i, ev (s i) ∈ k₀

def SepSt : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsThetaCompact F z i → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ →
    ∀ (d : ℕ) (J : Z.IdealSheafData) (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S), 1 ≤ d →
      (∀ x ∈ J.support, x ∉ Set.range i) → ValOn F i φ J d → IsNormBl π J → j ≫ π = i →
    ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (Q : Data V) (ξ : Sp V ⟶ S), UnifOver F j ξ Q →
    ∀ (m N : ℕ) (s : Fin m ⊕ Fin N → V) (ε : Module.Basis (Fin m ⊕ Fin N) ℤ (balForms (id : ℤ → ℤ) Q.X)) (τ₀ : Gens Q),
      Module.finrank ℤ Q.X ≤ g → IsCone id φ (fun k => (ε (.inl k) : LinearMap.BilinForm ℤ Q.X)) →
      (∀ x, x ≠ 0 → ∃ k, 0 < (ε (.inl k) : LinearMap.BilinForm ℤ Q.X) x x) →
      (∀ k, s (.inl k) ∈ maximalIdeal V ∧ s (.inl k) ≠ 0) → (∀ k, IsUnit (s (.inr k))) →
      TauIn Q τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (n : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ Q.X)) →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) → SepAt Q τ₀ s ev k₀

end GlobalTheory.Poinc.Sep
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IdlAlongNeTopOfValOn
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj

namespace GlobalTheory.Poinc.Basic₂

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ}

theorem trait_nonneg (T : Trait F) (x : T.D.toPre.X) : 0 ≤ T.β x x := by
  simpa using T.mono.nonneg 0 x

end GlobalTheory.Poinc.Basic₂
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsMumfordFamOfSubsingleton
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PolDeg

section Family

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {R : Type} [CommRing R] [IsDomain R]
  (y : Sp (FractionRing R) ⟶ F.X) {G₁ : Over (Sp R)} [GrpObj G₁] (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left)

def IsGenFibre : Prop := IsGrpPullback ((Over.pullback (jK R)).obj G₁) F.univ.A y α₁

def IsUnifAlong {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} (ρ : R →+* R') {G' : Over (Sp R')} [GrpObj G']
    [IsCommMonObj G'] (π : G'.left ⟶ G₁.left) {D : DegData R' I} {A : PolAV (Sp (FractionRing R'))} (U : Unif I D A G') : Prop :=
  IsGrpPullback G' G₁ (spMap ρ) π ∧
    ∃ (κ : Sp (FractionRing R') ⟶ Sp (FractionRing R)) (πK : pullback G'.hom (jK R') ⟶ pullback G₁.hom (jK R))
      (α : A.A.left ⟶ F.univ.A.left) (α₂ : (G2 A.A).left ⟶ (G2 F.univ.A).left),
      κ ≫ jK R = jK R' ≫ spMap ρ ∧ πK ≫ pullback.fst G₁.hom (jK R) = pullback.fst G'.hom (jK R') ≫ π ∧
        IsGrpPullback A.A F.univ.A (κ ≫ y) α ∧ IsSquare α α₂ ∧ LBIso (abelian₂ A.A A.L) (F.univ.P.pull α₂) ∧
        U.gen.hom.left ≫ α = πK ≫ α₁

def IsMumfordFam [IsLocalRing R] (Q : Data R) : Prop :=
  IsCN R ∧ Q.IsPos (maximalIdeal R) ∧
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U

variable {F y α₁}

theorem IsMumfordFam.isCN [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsCN R := h.1

theorem IsMumfordFam.isPos [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) : Q.IsPos (maximalIdeal R) := h.2.1

theorem IsMumfordFam.unif [IsLocalRing R] {Q : Data R} (h : IsMumfordFam F y α₁ Q) :
    ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'] (ρ : R →+* R'), IsCN R' → Function.Injective ρ → ρ.Finite →
    ∀ (D : DegData R' (maximalIdeal R')) (ε : D.toPre.X ≃+ Q.X), Refines Q ρ D.toPre ε →
      ∃ (G' : Over (Sp R')) (_ : GrpObj G') (_ : IsCommMonObj G') (π : G'.left ⟶ G₁.left) (A : PolAV (Sp (FractionRing R')))
        (U : Unif (maximalIdeal R') D A G'), IsUnifAlong F y α₁ ρ π U := h.2.2

end Family

section Charts

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} (F : SFam g n ζ) {S : Scheme.{0}} (s : S ⟶ Sp o) (j : F.X ⟶ S)

def PreChart [IsOpenImmersion j] (φ : InvFun ℤ) (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (R : Type) (_ : CommRing R) (_ : IsRegularLocalRing R) (_ : IsDomain R) (b : o →+* R) (ξ : Sp R ⟶ S) (m : ℕ)
    (t : Fin m → R) (Q : Data R) (δ : Fin m → LinearMap.BilinForm ℤ Q.X) (a : Fin m → ℕ)
    (G₁ : Over (Sp R)) (_ : GrpObj G₁) (y : Sp (FractionRing R) ⟶ F.X) (α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left),
    (IsAdicComplete (maximalIdeal R) R ∧ CharZero R ∧ ξ ≫ s = spMap b ∧ ξ (closedPoint R) = x ∧
      IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
      ((residue R).comp (Scheme.stalkClosedPointTo ξ).hom).FormallyUnramified) ∧
    (IsRelParam b t ∧ idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, t i} ∧
      ∀ p : Sp R, ξ p ∈ Set.range j ↔ ∏ i, t i ∉ p.asIdeal) ∧
    (IsSemiAbelian G₁ ∧ (∀ p : Sp R, p ∈ abLocus G₁ ↔ ∏ i, t i ∉ p.asIdeal) ∧ y ≫ j = jK R ≫ ξ ∧ IsGenFibre F y α₁) ∧
    (IsMumfordFam F y α₁ Q ∧ Module.finrank ℤ Q.X ≤ g ∧ IsCone id φ δ ∧ (∀ z, z ≠ 0 → ∃ i, 0 < δ i z z) ∧
      Q.IsMonomialTau t fun i => (n : ℤ) • δ i) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((n : ℤ) • δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, t i ^ a i}

end Charts

section Generic

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R']

theorem exists_genericMap {ρ : R →+* R'} (hρ : Function.Injective ρ) :
    ∃ κ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ ≫ jK R = jK R' ≫ spMap ρ := by
  have h : Function.Injective ((algebraMap R' (FractionRing R')).comp ρ) := (IsFractionRing.injective R' _).comp hρ
  refine ⟨spMap (IsFractionRing.lift (K := FractionRing R) h), ?_⟩
  change spMap _ ≫ spMap (algebraMap R (FractionRing R)) = spMap (algebraMap R' (FractionRing R')) ≫ spMap ρ
  rw [← spMap_comp, ← spMap_comp]
  congr 1
  ext r
  simp


omit [IsDomain R] in
theorem ne_zero_of_isRelParam {o : Type} [CommRing o] [IsLocalRing R] {b : o →+* R} {m : ℕ} {t : Fin m → R}
    (h : IsRelParam b t) (i : Fin m) : t i ≠ 0 := fun h0 => by
  have h₁ := h.mem_of_mem_sq (Pi.single i 1) (by
    rw [Finset.sum_eq_single i (fun k _ hk => by simp [Pi.single_eq_of_ne hk]) (by simp), h0, mul_zero]
    exact zero_mem _) i
  exact (maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using h₁))

end Generic

section Good

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem isSquare_comp {S S' S'' : Scheme.{0}} {G : Over S} {G' : Over S'} {G'' : Over S''} {φ : G'.left ⟶ G.left}
    {φ₂ : (G' ⊗ G').left ⟶ (G ⊗ G).left} {ψ : G''.left ⟶ G'.left} {ψ₂ : (G'' ⊗ G'').left ⟶ (G' ⊗ G').left}
    (h' : IsSquare ψ ψ₂) (h : IsSquare φ φ₂) : IsSquare (ψ ≫ φ) (ψ₂ ≫ φ₂) :=
  ⟨by rw [Category.assoc, h.1, ← Category.assoc, h'.1, Category.assoc],
    by rw [Category.assoc, h.2, ← Category.assoc, h'.2, Category.assoc]⟩

end Good

section Compare

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {s : S ⟶ Sp o} {j : F.X ⟶ S}
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left} {R : Type} [CommRing R] [IsDomain R]
  {y : Sp (FractionRing R) ⟶ F.X} {G₁ : Over (Sp R)} [GrpObj G₁] {α₁ : pullback G₁.hom (jK R) ⟶ F.univ.A.left}
  {ξ : Sp R ⟶ S} {π₁ : G₁.left ⟶ G.left}

theorem IsUnifAlong.isUnifOf (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {R' : Type} [CommRing R'] [IsDomain R'] {I : Ideal R'} {ρ : R →+* R'}
    {G' : Over (Sp R')} [GrpObj G'] [IsCommMonObj G'] {π : G'.left ⟶ G₁.left} {D : DegData R' I}
    {A : PolAV (Sp (FractionRing R'))} {U : Unif I D A G'} (h : IsUnifAlong F y α₁ ρ π U) :
    IsUnifOf F j e (spMap ρ ≫ ξ) (π ≫ π₁) U := by
  obtain ⟨hπ, κ, πK, α, α₂, hκ, hK, hA, hsq, hL, hU⟩ := h
  refine ⟨hπ.comp h₁, κ ≫ y, α, α₂, ?_, hA, hsq, hL, ?_⟩
  · rw [Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · rw [← Category.assoc, hU, Category.assoc, hα, ← Category.assoc, hK, Category.assoc]

theorem IsMumfordFam.isMumfordOf [IsLocalRing R] (h₁ : IsGrpPullback G₁ G ξ π₁) (hy : y ≫ j = jK R ≫ ξ)
    (hα : α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁) {Q : Data R} (h : IsMumfordFam F y α₁ Q) : IsMumfordOf F j e ξ Q := by
  refine ⟨h.isCN, h.isPos, fun R' _ _ _ ρ hR hρ hf D ε hD => ?_⟩
  obtain ⟨G', _, _, π, A, U, hU⟩ := h.unif R' ρ hR hρ hf D ε hD
  exact ⟨G', inferInstance, inferInstance, π ≫ π₁, A, U, hU.isUnifOf h₁ hy hα⟩

theorem IsGenFibre.exists_isGrpPullback [IsNoetherianRing R] [IsIntegrallyClosed R] (hG : IsSemiAbelian G)
    (he : IsGrpPullback F.univ.A G j e) (hG₁ : IsSemiAbelian G₁) (hy : y ≫ j = jK R ≫ ξ) (h : IsGenFibre F y α₁) :
    ∃ π₁ : G₁.left ⟶ G.left, IsGrpPullback G₁ G ξ π₁ ∧ α₁ ≫ e = pullback.fst G₁.hom (jK R) ≫ π₁ := by
  have h₀ := isGrpPullback_pullback G ξ
  have h₂ := (isGrpPullback_pullback ((Over.pullback ξ).obj G) (jK R)).comp h₀
  obtain ⟨E, hE, hE'⟩ := grpPullback_iso ((IsGrpPullback.comp h he).congr hy rfl) h₂
  obtain ⟨E₁, ⟨hE₁, hE₂⟩, -⟩ := GlobalTheory.SemiAbExtDomain.existsUnique_iso_extension_generic (FractionRing R) G₁
    ((Over.pullback ξ).obj G) hG₁ (IsSemiAbelian.pullback ξ G hG) E
  refine ⟨E₁.hom.left ≫ pullback.fst G.hom ξ, ((isGrpPullback_of_iso E₁).comp h₀).congr (Category.id_comp _) rfl, ?_⟩
  have h₃ : ((Over.pullback (jK R)).map E₁.hom).left ≫ pullback.fst ((Over.pullback ξ).obj G).hom (jK R) =
      pullback.fst G₁.hom (jK R) ≫ E₁.hom.left := pullback.lift_fst _ _ _
  have h₄ : E.hom = (Over.pullback (jK R)).map E₁.hom := hE₂.symm
  refine hE'.symm.trans ?_
  rw [h₄]
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst G.hom ξ) h₃).trans (Category.assoc _ _ _))

variable [IsOpenImmersion j] {φ : InvFun ℤ} {BD : EffCartierData S} {d : ℕ} {x : S}

theorem PreChart.hasPolChart (hG : IsSemiAbelian G) (he : IsGrpPullback F.univ.A G j e) (h : PreChart F s j φ BD d x) :
    HasPolChart F s j e φ BD d x := by
  obtain ⟨R, _, _, _, b, ξ, m, t, Q, δ, a, G₁, _, y, α₁, c₁, c₂, ⟨hG₁, -, hy, hα⟩, ⟨hM, c₃⟩, c₄⟩ := h
  have := (GlobalTheory.isDomain_and_isIntegrallyClosed_of_isRegularLocalRing R).2
  obtain ⟨π₁, h₁, h₂⟩ := hα.exists_isGrpPullback hG he hG₁ hy
  exact ⟨R, inferInstance, inferInstance, inferInstance, b, ξ, m, t, Q, δ, a, c₁, c₂, ⟨hM.isMumfordOf h₁ hy h₂, c₃⟩, c₄⟩

end Compare

end GlobalTheory.PolDeg
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyIso
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.UPel.HT.RepFamModel
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]

theorem objMap_refl {b : Base D R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) :
    Nonempty (ObjMap o o (𝟙 S)) :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }⟩

variable {b : Base D R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R}
  {o₁ : Obj b N s₁} {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}

end GlobalTheory.UPel.HT.RepFamModel
end
end

