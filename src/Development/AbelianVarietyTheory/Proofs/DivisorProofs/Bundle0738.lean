module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0557
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0573
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.PolarizedAbelianEmbeddingBySections
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.NotTrivialAndTwist
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0719

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CommutatorPairingSwapEqOfSwapInvariant
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SwapPairing

theorem weilIs_swap_eq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (P : LB (G2 A).left), IsAbelianScheme A → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (n : ℤ) (T : Over S) (u v : T ⟶ A) (c c' : Γ(T.left, ⊤)ˣ), Out.WeilIs (G2 A) P n (lift 1 u) (lift v 1) c → Out.WeilIs (G2 A) P n (lift u 1) (lift 1 v) c' → c = c' := by
  intro S A _ _ P hA hP hiso n T u v c c' h h'
  let ψ : G2 A ⟶ G2 A := lift (snd A A) (fst A A)
  haveI : IsMonHom ψ := inferInstanceAs (IsMonHom (lift (snd A A) (fst A A)))
  have hAA : IsAbelianScheme (G2 A) := AbelianSchemeGerms.isAbelianScheme_tensor A A hA hA
  have hx : lift u 1 ≫ ψ = lift 1 u := by ext <;> simp [ψ]
  have hy : lift 1 v ≫ ψ = lift v 1 := by ext <;> simp [ψ]
  have hw : LBIso (lbPow P 1) (P.pull ψ.left) :=
    LBIso.trans (isLB_lbPow hP 1) hP (pull_isLB hP _) (lbIso_lbPow_one hP) hiso
  have h1 := WeilIsogeny.weilIs_pull_hom (d := 1) (x := lift u 1) (y := lift 1 v)
    globalFns_holds hAA hP hP ψ hw (by rw [hx, hy]; exact h)
  rw [Nat.cast_one, _root_.mul_one] at h1
  exact CommutatorPairing.weilIs_unique globalFns_holds hAA hP h1 h'

end GlobalTheory.SwapPairing
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixUniv

variable {A₀ B₀ X T : Scheme.{0}} {N : LB A₀} {H : LB B₀} {mA mB : ℕ}

def comb (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) (z : X) (q : N.ι)
    (j : Fin mB) : X.presheaf.stalk z :=
  ∑ i, gs p z ⊤ (c i j) * gs φ z (N.U q) ((a i).f q)

def Generates (a : Fin mA → LB.Sec N) (φ : X ⟶ A₀) (p : X ⟶ T) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q, φ z ∈ N.U q → ∃ j, IsUnit (comb a φ p c z q j)

def Proport (a : Fin mA → LB.Sec N) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀) (p : X ⟶ T) (Ψ : X ⟶ B₀)
    (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ z q k, φ z ∈ N.U q → Ψ z ∈ H.U k → ∀ j j',
    gs Ψ z (H.U k) ((b j).f k) * comb a φ p c z q j' = gs Ψ z (H.U k) ((b j').f k) * comb a φ p c z q j

def gc {R : Type} [CommRing R] (f : X ⟶ Sp R) (z : X) : R →+* X.presheaf.stalk z :=
  (X.presheaf.germ ⊤ z trivial).hom.comp (f.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)

def Kills {R : Type} [CommRing R] (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (F : MvPolynomial (Fin mB) R) : Prop :=
  ∀ k, MvPolynomial.eval₂Hom (GlobalTheory.AbLaw.cst fB (H.U k)) (fun j => (b j).f k) F = 0

def FormsOK {R : Type} [CommRing R] (a : Fin mA → LB.Sec N) (fB : B₀ ⟶ Sp R) (b : Fin mB → LB.Sec H) (φ : X ⟶ A₀)
    (p : X ⟶ T) (t : T ⟶ Sp R) (c : Fin mA → Fin mB → Γ(T, ⊤)) : Prop :=
  ∀ (d : ℕ) (F : MvPolynomial (Fin mB) R), F.IsHomogeneous d → Kills fB b F →
    ∀ z q, φ z ∈ N.U q → MvPolynomial.eval₂Hom (gc (p ≫ t) z) (comb a φ p c z q) F = 0

def IsVal {S : Scheme.{0}} (e : S ⟶ A₀) (u : ∀ z : S, N.ι → (S.presheaf.stalk z)ˣ) (s : LB.Sec N) (α : Γ(S, ⊤)) :
    Prop :=
  ∀ z q, e z ∈ N.U q → gs e z (N.U q) (s.f q) = gs (𝟙 S) z ⊤ α * (u z q).val

def Normal {S : Scheme.{0}} (t : T ⟶ S) (c : Fin mA → Fin mB → Γ(T, ⊤)) (α : Fin mA → Γ(S, ⊤)) (β : Fin mB → Γ(S, ⊤)) :
    Prop :=
  ∀ j, t.appTop (β j) = ∑ i, c i j * t.appTop (α i)

def θ {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : A.left ⟶ (topS Rg ⊗ A).left :=
  (lift (Over.homMk (A.hom ≫ (Sp Rg).topIso.inv) (by simp) : A ⟶ topS Rg) (𝟙 A)).left

theorem θ_snd {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : θ A ≫ (snd (topS Rg) A).left = 𝟙 A.left := by
  rw [θ, ← Over.comp_left, lift_snd]; rfl

abbrev fA {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) : (topS Rg ⊗ A).left ⟶ Sp Rg := (topS Rg ⊗ A).hom

theorem coord_comp {Rg : Type} [CommRing Rg] {X' : Scheme.{0}} {n : ℕ} (h : X ⟶ X')
    (g : X' ⟶ Sp (MvPolynomial (Fin n) Rg)) (i : Fin n) : coord (h ≫ g) i = h.appTop (coord g i) := by
  rfl

def uFr {Rg : Type} [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (L : LB A.left) (k : ℕ)
    (eA : LB.Gen (L.pull (eSec A))) (z : (𝟙_ (Over (Sp Rg))).left) (q : (LPow A L (k : ℤ) (topS Rg)).ι) :
    ((𝟙_ (Over (Sp Rg))).left.presheaf.stalk z)ˣ :=
  (gm (𝟙 _) z _ (eA.s fun _ => q 0)) ^ k

end GlobalTheory.HomFixUniv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoupledClassSumCauchySchwarz
section
noncomputable section

namespace GlobalTheory.ColNorms.CplCS

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds GlobalTheory.ColNorms
open scoped ComplexOrder Matrix

theorem diag_sum_le {V ι : Type} [AddCommGroup V] (B : V →+ V →+ ℝ) (hB : ∀ x, 0 ≤ B x x) (s : Finset ι) (x : ι → V) :
    B (∑ i ∈ s, x i) (∑ i ∈ s, x i) ≤ s.card * ∑ i ∈ s, B (x i) (x i) := by
  have h1 : ∀ a b, B a b + B b a ≤ B a a + B b b := by
    intro a b
    have := hB (a - b)
    simp only [map_sub, AddMonoidHom.sub_apply] at this
    linarith
  have e : B (∑ i ∈ s, x i) (∑ i ∈ s, x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum B x s, AddMonoidHom.finsetSum_apply]
    exact Finset.sum_congr rfl fun i _ => map_sum _ _ _
  have e' : ∑ i ∈ s, ∑ j ∈ s, B (x j) (x i) = ∑ i ∈ s, ∑ j ∈ s, B (x i) (x j) := Finset.sum_comm
  have h2 : ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x j) + B (x j) (x i)) ≤ ∑ i ∈ s, ∑ j ∈ s, (B (x i) (x i) + B (x j) (x j)) :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => h1 _ _
  simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at h2
  rw [e]
  linarith

variable {K : Type} [Field K] [NumberField K] [StarRing K]

def reForm (S : GSD K) (v : InfinitePlace K) : S.V →+ S.V →+ ℝ :=
  AddMonoidHom.mk' (fun x => AddMonoidHom.mk' (fun y => (S.pairAt v x y).re) (by
      intro y z
      simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, mul_add, Finset.sum_add_distrib, Complex.add_re]))
    (by
      intro x y
      ext z
      simp only [GSD.pairAt, map_add (f := _), Finsupp.add_apply, add_mul, Finset.sum_add_distrib, Complex.add_re,
        AddMonoidHom.mk'_apply, AddMonoidHom.add_apply])

theorem sq_nonneg' {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (x : S.V) : 0 ≤ (S.pairAt v x x).re := by
  have e : S.pairAt v x x = star (fun i => v.embedding (S.bV.repr x i)) ⬝ᵥ
      S.gramV.map v.embedding *ᵥ fun i => v.embedding (S.bV.repr x i) := by
    simp only [GSD.pairAt, dotProduct, Matrix.mulVec, Finset.mul_sum, Matrix.map_apply, Pi.star_apply, starRingEnd_apply,
      mul_assoc]
  rw [e]
  exact (Complex.nonneg_iff.1 (Matrix.PosSemidef.dotProduct_mulVec_nonneg h _)).1

theorem sq_sum_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) {ι : Type} (s : Finset ι) (x : ι → S.V) {m : ℝ}
    (hm : (s.card : ℝ) ≤ m) :
    (S.pairAt v (∑ i ∈ s, x i) (∑ i ∈ s, x i)).re ≤ m * ∑ i ∈ s, (S.pairAt v (x i) (x i)).re :=
  (diag_sum_le (reForm S v) (sq_nonneg' h) s x).trans
    (mul_le_mul_of_nonneg_right hm (Finset.sum_nonneg fun _ _ => sq_nonneg' h _))

theorem inv_nat_le_one (n : ℕ) : ((n : ℝ))⁻¹ ≤ 1 := Nat.cast_inv_le_one n

theorem sq_smul_le {S : GSD K} {v : InfinitePlace K} (h : PosAt S v) (n : ℕ) (x : S.V) :
    (S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x)).re ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := by
  have e : S.pairAt v ((n : K)⁻¹ • x) ((n : K)⁻¹ • x) = (((n : ℝ)⁻¹ * (n : ℝ)⁻¹ : ℝ) : ℂ) * S.pairAt v x x := by
    simp only [GSD.pairAt, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, map_inv₀, map_natCast, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring
  rw [e, Complex.re_ofReal_mul, mul_assoc]
  have h0 : (0 : ℝ) ≤ (n : ℝ)⁻¹ * (S.pairAt v x x).re := mul_nonneg (by positivity) (sq_nonneg' h x)
  exact mul_le_of_le_one_left h0 (inv_nat_le_one n)

theorem ipAt_re (S : GSD K) (h : S.Ok) (v : InfinitePlace K) (φ : S.D → S.V) :
    (S.ipAt h v φ φ).re = letI := h.fintypeCl
      ∑ c : S.Cl, (((S.toCSD h).wt c : ℕ) : ℝ)⁻¹ * (S.pairAt v (φ (S.outSec.rep c)) (φ (S.outSec.rep c))).re := by
  unfold GSD.ipAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Complex.re_ofReal_mul]
  push_cast
  rfl

theorem comp_opLe {S₀ S S₁ : GSD K} {Y : Cpl S} (A : CplKer S₀ S S₁ Y) (hS : S.Ok) (v : InfinitePlace K)
    {t₁ t₂ h ny : ℝ} (ht₁ : 0 ≤ t₁) (ht₂ : 0 ≤ t₂) (hh : 0 ≤ h) (hny : 0 ≤ ny) (p₀ : PosAt S₀ v) (p₁ : PosAt S₁ v)
    (hc : (Nat.card S.Cl : ℝ) ≤ h) (hy : ∀ d, ((Y.ys d).ncard : ℝ) ≤ ny)
    (h1 : ∀ d₀ d, ∀ y ∈ Y.ys d, OpLe S₀ S v (A.k1 d₀ d y) t₁) (h2 : ∀ d d₁, ∀ y ∈ Y.ys d, OpLe S S₁ v (A.k2 d y d₁) t₂)
    (d₀ : S₀.D) (d₁ : S₁.D) : OpLe S₀ S₁ v ((A.comp hS S.outSec).k d₀ d₁) (h ^ 2 * ny ^ 2 * t₁ * t₂) := by
  intro x
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  have hx := sq_nonneg' p₀ x
  have e : (A.comp hS S.outSec).k d₀ d₁ x = ∑ c : S.Cl, (((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x) := by
    simp only [CplKer.comp, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]
  rw [e]
  refine (sq_sum_le p₁ _ _ hc').trans ?_
  have key : ∀ c : S.Cl, (S₁.pairAt v ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))
      ((((S.toCSDOf hS S.outSec).wt c : K))⁻¹ •
      ∑ y ∈ (Y.fin (S.outSec.rep c)).toFinset, A.k2 (S.outSec.rep c) y d₁ (A.k1 d₀ (S.outSec.rep c) y x))).re ≤
      ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))) := by
    intro c
    have hy' : (((Y.fin (S.outSec.rep c)).toFinset.card : ℕ) : ℝ) ≤ ny := by
      rw [← Set.ncard_eq_toFinset_card _ (Y.fin _)]
      exact hy _
    refine (sq_smul_le p₁ _ _).trans ((mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans ?_)
    refine (sq_sum_le p₁ _ _ hy').trans (mul_le_mul_of_nonneg_left ?_ hny)
    refine (Finset.sum_le_card_nsmul _ _ (t₂ * (t₁ * (S₀.pairAt v x x).re)) fun y hy => ?_).trans ?_
    · have hy0 : y ∈ Y.ys (S.outSec.rep c) := (Set.Finite.mem_toFinset _).1 hy
      exact (h2 _ _ y hy0 _).trans (mul_le_mul_of_nonneg_left (h1 _ _ y hy0 _) ht₂)
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right hy' (by positivity)
  have h3 := Finset.sum_le_card_nsmul Finset.univ _ _ fun c _ => key c
  rw [nsmul_eq_mul] at h3
  calc _ ≤ h * (h * (ny * (ny * (t₂ * (t₁ * (S₀.pairAt v x x).re))))) :=
        mul_le_mul_of_nonneg_left (h3.trans (mul_le_mul_of_nonneg_right hc' (by positivity))) hh
    _ = _ := by ring

theorem appOf_le {S S' : GSD K} (A : ClsKer S S') (hS : S.Ok) (v : InfinitePlace K) {t h : ℝ} (hh : 0 ≤ h)
    (p' : PosAt S' v) (hc : (Nat.card S.Cl : ℝ) ≤ h) (hA : ∀ d d', OpLe S S' v (A.k d d') t) (φ : S.D → S.V) (d' : S'.D) :
    (S'.pairAt v (A.appOf hS S.outSec φ d') (A.appOf hS S.outSec φ d')).re ≤ h * (t * (S.ipAt hS v φ φ).re) := by
  letI := hS.fintypeCl
  have hc' : ((Finset.univ : Finset S.Cl).card : ℝ) ≤ h := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  unfold ClsKer.appOf
  refine (sq_sum_le p' _ _ hc').trans (mul_le_mul_of_nonneg_left ?_ hh)
  rw [ipAt_re, Finset.mul_sum]
  refine Finset.sum_le_sum fun c _ => (sq_smul_le p' _ _).trans ?_
  rw [mul_left_comm]
  exact mul_le_mul_of_nonneg_left (hA _ _ _) (by positivity)

theorem cpl_le : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Q : KerChain K) (v : InfinitePlace K) (t₁ t₂ h₀ h h₁ ny : ℝ), 0 ≤ t₁ → 0 ≤ t₂ → 0 ≤ h₀ → 0 ≤ h → 0 ≤ h₁ → 0 ≤ ny → (∀ b, PosAt ((Q.F Q.n).mem b) v) → PosAt Q.S v → PosAt Q.S₁ v → (∀ b, (Nat.card ((Q.F Q.n).mem b).Cl : ℝ) ≤ h₀) → (Nat.card Q.S.Cl : ℝ) ≤ h → (Nat.card Q.S₁.Cl : ℝ) ≤ h₁ → (∀ d, ((Q.Y.ys d).ncard : ℝ) ≤ ny) → (∀ b d₀ d, ∀ y ∈ Q.Y.ys d, OpLe ((Q.F Q.n).mem b) Q.S v ((Q.cp b).k1 d₀ d y) t₁) → (∀ b d d₁, ∀ y ∈ Q.Y.ys d, OpLe Q.S Q.S₁ v ((Q.cp b).k2 d y d₁) t₂) → ∀ φ : (Q.F Q.n).Forms, (Q.S₁.ipAt Q.hS₁ v (Q.cpl φ) (Q.cpl φ)).re ≤ (Fintype.card (Q.F Q.n).β : ℝ) * h₀ * h ^ 2 * h₁ * ny ^ 2 * t₁ * t₂ * (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
  intro K _ _ _ Q v t₁ t₂ h₀ h h₁ ny ht₁ ht₂ hh₀ hh hh₁ hny p₀ _ p₁ c₀ c c₁ hy k1 k2 φ
  letI := Q.hS₁.fintypeCl
  have hc' : ((Finset.univ : Finset Q.S₁.Cl).card : ℝ) ≤ h₁ := by
    rwa [Finset.card_univ, ← Nat.card_eq_fintype_card]
  set M : ℝ := (Fintype.card (Q.F Q.n).β : ℝ) * (h₀ * (h ^ 2 * ny ^ 2 * t₁ * t₂ *
    (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re)) with hM
  have key : ∀ d : Q.S₁.D, (Q.S₁.pairAt v ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d) ((Q.cpl φ : Q.S₁.D → Q.S₁.V) d)).re ≤ M := by
    intro d
    have e : (Q.cpl φ : Q.S₁.D → Q.S₁.V) d = ∑ b : (Q.F Q.n).β,
        ((Q.cp b).comp Q.hS Q.S.outSec).appOf (Q.hF Q.n b) ((Q.F Q.n).mem b).outSec (φ b) d := by
      simp only [KerChain.cpl, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum, Finset.sum_apply]
      rfl
    rw [e]
    refine (sq_sum_le p₁ _ _ (le_of_eq (by rw [Finset.card_univ]))).trans
      (mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _))
    unfold famIpAt
    rw [Complex.re_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ => appOf_le _ _ v hh₀ p₁ (c₀ b)
      (comp_opLe (Q.cp b) Q.hS v ht₁ ht₂ hh hny (p₀ b) p₁ c hy (k1 b) (k2 b)) _ _
  have hF : 0 ≤ (famIpAt (Q.F Q.n) (Q.hF Q.n) v φ φ).re := by
    unfold famIpAt
    rw [Complex.re_sum]
    refine Finset.sum_nonneg fun b _ => ?_
    rw [ipAt_re]
    exact Finset.sum_nonneg fun c _ => mul_nonneg (by positivity) (sq_nonneg' (p₀ b) _)
  have hM0 : 0 ≤ M := by positivity
  rw [ipAt_re]
  refine (Finset.sum_le_card_nsmul _ _ M fun c _ =>
    (mul_le_of_le_one_left (sq_nonneg' p₁ _) (inv_nat_le_one _)).trans (key _)).trans ?_
  rw [nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right hc' hM0).trans (le_of_eq ?_)
  rw [hM]
  ring

end GlobalTheory.ColNorms.CplCS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartan
section
noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.RealPar Matrix

namespace GlobalTheory.CoverExp

variable {p q : ℕ}

theorem sq_expt (T : GrpData p q) {X : Mat p q} (hX : X ∈ upq p q) :
    ((T.sq (T.expt X) : ℂˣ) : ℂ) = Complex.exp (X.trace / 2) := by
  set c : ℂ := X.trace / 2 with hc
  set f : ℝ → ℂ := fun t => ((T.sq (T.expt (t • X)) : ℂˣ) : ℂ) with hf
  have hd : ∀ t, HasDerivAt f (f t * c) t := by
    intro t
    have h0 : HasDerivAt f c 0 := Cover.hasDerivAt_sq (T := T) hX
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) c t :=
      HasDerivAt.comp_sub_const t t (f := f) (f' := c) (by rw [sub_self]; exact h0)
    have h2 : f = fun s => f t * f (s - t) := by
      funext s
      simp only [hf]
      rw [← Units.val_mul, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    have h3 := h1.const_mul (f t)
    rw [← h2] at h3
    exact h3
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) * f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    exact (h1.fun_mul (hd t)).congr_deriv (by ring)
  have h := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, Units.val_one] at h
  calc _ = Complex.exp c * (Complex.exp (-c) * ((T.sq (T.expt X) : ℂˣ) : ℂ)) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = _ := by rw [h, mul_one]

theorem exists_expt_ker (hn : 1 ≤ p + q) (T : GrpData p q) :
    ∃ Z ∈ upq p q, T.cov (T.expt Z) = 1 ∧ T.sq (T.expt Z) = -1 := by
  let a : Ix p q := finSumFinEquiv.symm ⟨0, hn⟩
  refine ⟨TorusWt.torX (Pi.single a (2 * Real.pi)), TorusWt.torX_mem _, ?_, ?_⟩
  · apply Units.ext
    rw [T.expt_cov _ (TorusWt.torX_mem _), TorusWt.torX, Matrix.exp_diagonal, Units.val_one, ← Matrix.diagonal_one]
    congr 1
    funext b
    rw [Pi.coe_exp, ← Complex.exp_eq_exp_ℂ]
    by_cases h : b = a
    · subst h
      simp [Complex.exp_two_pi_mul_I]
    · simp [h]
  · apply Units.ext
    rw [sq_expt T (TorusWt.torX_mem _), TorusWt.torX, Matrix.trace_diagonal, Finset.sum_eq_single a]
    · rw [Pi.single_eq_same, show ((2 * Real.pi : ℝ) : ℂ) * Complex.I / 2 = Real.pi * Complex.I by push_cast; ring,
        Complex.exp_pi_mul_I]
      simp
    · intro b _ h
      simp [h]
    · simp

theorem exists_blockOrd (p q : ℕ) : ∃ (e : Ix p q ≃ Fin (p + q)) (ε : Fin (p + q) → Bool), BlockOrd e ε := by
  refine ⟨finSumFinEquiv, fun i => (finSumFinEquiv.symm i).isLeft, fun i => by simp, fun j => by simp, ?_⟩
  rintro (a | a) (b | b) h
  · have h' : a < b := h
    exact h'
  · exact h.elim
  · exact h.elim
  · have h' : a < b := h
    exact Nat.add_lt_add_left h' p

theorem isPC_of_anticomm {X : Mat p q} (h : X * Jm p q = -(Jm p q * X)) : IsPC X := by
  intro a b hab
  have := congrFun (congrFun h a) b
  rw [Matrix.neg_apply, KStabLie.Jm_eq, Matrix.mul_diagonal, Matrix.diagonal_mul] at this
  rcases a with a | a <;> rcases b with b | b
  · simp only [Sum.elim_inl] at this
    linear_combination (1 / 2 : ℂ) * this
  · simp [sameBlock] at hab
  · simp [sameBlock] at hab
  · simp only [Sum.elim_inr] at this
    linear_combination (-1 / 2 : ℂ) * this

theorem exists_exp_mul_exp {g : Mat p q} (hg : gᴴ * Jm p q * g = Jm p q) :
    ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, g = NormedSpace.exp Z * NormedSpace.exp X := by
  obtain ⟨e, ε, hb⟩ := exists_blockOrd p q
  obtain ⟨Z, X, hZ, hX, h⟩ := Formalism.REAL.genExp_of Formalism.REAL.compact_exponential_surjective _ ε _ ((hb.inUJ_iff g).2 hg)
  obtain ⟨Z, rfl⟩ := (Matrix.reindex e e).surjective Z
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective X
  have hG : ∀ Y : Mat p q, Formalism.REAL.inG ε (Matrix.reindex e e Y) → Y ∈ upq p q := by
    intro Y h1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_add]
    exact h1
  have hexp : ∀ Y : Mat p q, NormedSpace.exp (Matrix.reindex e e Y) = Matrix.reindex e e (NormedSpace.exp Y) := by
    intro Y
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) Y).symm
  refine ⟨Z, hG Z hZ.1, (KStabLie.isKC_iff Z).2 ?_, X, ⟨hG X hX.1, isPC_of_anticomm ?_⟩, ?_⟩
  · have h2 := hZ.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h2
  · have h2 := hX.2
    rw [← hb.reindex_Jm] at h2
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h2
    exact h2
  · rw [hexp, hexp] at h
    apply (Matrix.reindex e e).injective
    simpa only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] using h

theorem closure_expt_eq_top_and_cartan : ∀ (p q : ℕ), 1 ≤ p + q → ∀ T : GrpData p q,
    Subgroup.closure (T.expt '' upq p q) = ⊤ ∧ ∀ g : T.G, ∃ k ∈ T.Kset, ∃ Y ∈ pR p q, g = k * T.expt Y := by
  intro p q hn T
  have key : ∀ g : T.G, ∃ Z ∈ upq p q, IsKC Z ∧ ∃ X ∈ pR p q, T.cov g = T.cov (T.expt Z) * T.cov (T.expt X) := by
    intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := exists_exp_mul_exp ((mem_Upq _).1 (T.cov_mem g))
    exact ⟨Z, hZ, hK, X, hX, Units.ext (by rw [Units.val_mul, T.expt_cov Z hZ, T.expt_cov X hX.1, h])⟩
  constructor
  · rw [eq_top_iff]
    intro g _
    obtain ⟨Z, hZ, -, X, hX, h⟩ := key g
    obtain ⟨C, hC, hC1, hC2⟩ := exists_expt_ker hn T
    have hm : ∀ Y ∈ upq p q, T.expt Y ∈ Subgroup.closure (T.expt '' upq p q) :=
      fun Y hY => Subgroup.subset_closure ⟨Y, hY, rfl⟩
    have hx := Subgroup.mul_mem _ (hm Z hZ) (hm X hX.1)
    rw [← map_mul] at h
    set x := T.expt Z * T.expt X
    have h2 : ((T.sq g : ℂˣ) : ℂ) ^ 2 = ((T.sq x : ℂˣ) : ℂ) ^ 2 := by rw [T.sq_sq, T.sq_sq, h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.1 h2 with h3 | h3
    · rw [Cover.ext_of h (Units.ext h3)]
      exact hx
    · have : g = T.expt C * x := Cover.ext_of (by rw [map_mul, hC1, one_mul, h])
        (Units.ext (by rw [map_mul, hC2, h3]; simp))
      rw [this]
      exact Subgroup.mul_mem _ (hm C hC) hx
  · intro g
    obtain ⟨Z, hZ, hK, X, hX, h⟩ := key g
    refine ⟨g * (T.expt X)⁻¹, ?_, X, hX, by simp⟩
    have h1 := KStabLie.expt_mem T hZ hK 1
    rw [one_smul] at h1
    change IsKC _
    rw [map_mul, map_inv, h, mul_inv_cancel_right]
    exact h1

end GlobalTheory.CoverExp

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfPullDensePartOfPullSection
section
open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CechPic

theorem eq_zero_of_pull_densePart_of_pull_section : ∀ {S Y U YU : Scheme.{0}} [IsLocallyNoetherian S]
    [GlobalTheory.IsNormalScheme S] (f : Y ⟶ S) [Smooth f] [GeometricallyConnected f] (j : U ⟶ S)
    [IsOpenImmersion j] (ρ : YU ⟶ Y) (fU : YU ⟶ U), Dense (Set.range j) → IsPullback ρ fU f j →
    ∀ σ : S ⟶ Y, σ ≫ f = 𝟙 S → ∀ δ : GlobalTheory.CechPic.Pic Y, GlobalTheory.CechPic.pull ρ δ = 0 →
      GlobalTheory.CechPic.pull σ δ = 0 → δ = 0 := by
  intro S Y U YU _ _ f _ _ j _ ρ fU hd hpb σ hσ δ hρ hσδ
  obtain ⟨N, hN, rfl⟩ := cls_surj δ
  have hdom : IsDominant j := ⟨hd⟩
  have hgi : GeometricallyIntegral f :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected Y S f inferInstance inferInstance
  have hfst : pullback.fst f j = hpb.isoPullback.inv ≫ ρ := (IsPullback.isoPullback_inv_fst hpb).symm
  have h1 : cls (N.pull σ) (pull_isLB hN σ) = 0 := by rw [cls_pull hN]; exact hσδ
  have h2 : cls (N.pull (pullback.fst f j)) (pull_isLB hN _) = 0 := by
    rw [cls_pull hN, hfst, pull_comp, hρ, map_zero]
  obtain ⟨t, ht⟩ := GlobalTheory.GenericExtend.exists_isGen_of_densePart S U j (GlobalTheory.IsNormalScheme.pred S)
    inferInstance inferInstance hdom inferInstance (Over.mk f) σ N hσ (show Smooth f from inferInstance) hgi hN
    ((cls_eq_zero_iff _).1 h1) ((cls_eq_zero_iff _).1 h2)
  exact (cls_eq_zero_iff hN).2 ⟨t, ht⟩

end GlobalTheory.CechPic
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBirigidifiedBundleOfDescentStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_birigidified_bundle_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (M : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b M s) (A' : Over S) [GrpObj A'] [IsCommMonObj A'] (ψ : o.A ⟶ A'), IsMonHom ψ → ∀ (m : ℕ) (P₀ : LB (G2 A').left), P₀.IsLB → LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P₀.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) → ∃ P' : LB (G2 A').left, P'.IsLB ∧ (∃ t : (P'.pull (lift (1 : A' ⟶ A') (𝟙 A')).left).Gen, t.IsGen) ∧ (∃ t : (P'.pull (lift (𝟙 A') (1 : A' ⟶ A')).left).Gen, t.IsGen) ∧ LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P m) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)) := by
  first | (exact @GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (exact GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent) | (intros; apply GlobalTheory.UPel.HT.Hecke.exists_birigidified_of_descent  <;> assumption)
end

