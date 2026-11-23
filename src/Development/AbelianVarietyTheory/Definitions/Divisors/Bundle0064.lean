module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2091
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.BudgetAt
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.BigTop

namespace GlobalTheory.CovHt

section Steps

open _root_.Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (Y : Cov p i)

def ShortAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ abelian₂ : ℝ, (∀ Z, ∃ (n : ℕ) (w : Fin n → cuspOn Y.U Z (wtOf (dat p i) u1 0)),
      IsShortGen (normOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0))
        (latOn Y.U Z (wtOf (dat p i) u1 0)) w abelian₂) ∧
    Real.log abelian₂ * (6 * dimFlag (dat p i) + 10 + lenT p i PP * (zed p i PP u1 + 2 * rhoB (dat p i) u1)) ≤ C * unitE p

def GeomAt (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∀ Z, GoodOn Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z (wtOf (dat p i) u1 0) ∧
    GlobalTheory.DegVal.BirOn Y.U Z (wtOf (dat p i) u1 0) ∧ (1 - rhoB (dat p i) u1) * Y.dg u1 Z ≤ delPrime Y.U Z u1

def MultAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  ∃ cc : ℝ, 0 ≤ cc ∧ lenT p i PP * cc ≤ C * unitE p ∧
    ∀ Z, Mult Y.U (xiR D) (fun _ => D.sp.W ((i : ℕ) + 1)) Y.dict Z u1 (uPrime (dat p i) u1) cc

def BudgetAt (PP C : ℝ) (u1 : AllWt.Weight (dat p i)) : Prop :=
  Y.d.l₂.M'.primeFactors.card ≤ 15 ∧
  ∃ g : ℝ, WtGap (uPrime (dat p i) u1) g ∧ 0 ≤ errX (ell D) (uPrime (dat p i) u1) g ∧
    lenT p i PP * errX (ell D) (uPrime (dat p i) u1) g ≤ C * unitE p ∧
    0 ≤ htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) ∧
    lenT p i PP * (htCost Y.d.l₂ (bndB (uPrime (dat p i) u1) g) * l1 (uPrime (dat p i) u1)) ≤ C * unitE p

end Steps

end GlobalTheory.CovHt

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfHasRepUnit
section
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon.Model

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem fam_ev {U T : Over S} {M : LB (A ⊗ U).left} (h : Fam A M) (u : T ⟶ U) :
    Fam A (ev M (fst A T) (snd A T ≫ u)) := by
  have hM : (ev M (fst A T) (snd A T ≫ u)).IsLB := pull_isLB h.isLB _
  refine ⟨hM, (isAdditive_iff hM).2 fun Y a a' t ↦ ?_⟩
  simp only [evc_ev h.isLB, lift_fst, lift_snd_assoc]
  exact (isAdditive_iff h.isLB).1 h.add Y a a' _

theorem rep_ext {B S' Y : Over S} {b : B ⟶ S'} {P : LB (A ⊗ B).left} (h : Rep A b P) {u u' : Y ⟶ B}
    (hb : u ≫ b = u' ≫ b) (e : Same A P P u u') : u = u' := by
  have hu := fam_ev h.fam u
  exact (h.univ Y (u ≫ b) _ hu).unique ⟨rfl, (cls_eq_iff hu.isLB hu.isLB).1 rfl⟩ ⟨hb.symm, e⟩




end GlobalTheory.DualCon.Model
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.EtLevForget
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.EtLev
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Gen
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.EtC GlobalTheory.UPel.HT GlobalTheory.PELU GlobalTheory.KS
open scoped TensorProduct Matrix

namespace GlobalTheory.EtaleLevelHecke

def ModelExists : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → Nonempty (Model b N)

def ModelProj : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsDomain R] [CharZero R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.CompactB → ∀ M : Model b N, IsProjOver M.s

def GenCmp : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (R' : Type) [CommRing R'] [Algebra ℚ R'] (φ : R →+* R') (gb : GBase D.toG R'), gb.ρ = φ b.ρ → (∀ i, gb.t i = φ.comp (b.t i)) → ∀ (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (M : Model b N) (X : GenModel gb N), ∃ j : X.X ⟶ pullback M.s (spMap φ), IsOpenImmersion j ∧ IsClosedImmersion j ∧ j ≫ pullback.snd _ _ = X.s ∧ IsGPull X.univ M.univ (j ≫ pullback.fst _ _)

end GlobalTheory.EtaleLevelHecke
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.VB

namespace GlobalTheory.CovTest

def IsFlagBundle {B Y : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) : Prop :=
  ∀ (T : Scheme.{0}) (g : T ⟶ B) (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)),
    ∃! g' : T ⟶ Y, ∃ w : g' ≫ π = g, ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
      e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
        (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)



open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.DegreeFormula Formalism.MainNotions.WeightThresholdDefs GlobalTheory.FlagPoly GlobalTheory.FlagAr GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam.Pad

section One

variable {D : D7} (Y : ShimX D.what₂.Tau)


def bcFl : ℝ := (1 / (Y.j : ℝ) - 1 / ((Y.N : ℝ) - Y.j)) * testI Y

end One

def rkB (ι : Type) (N j : ℕ) (a : ι × Bool) : ℕ := cond a.2 j (N - j)

end GlobalTheory.CovTest

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FacAlg
section
noncomputable section

open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.Mum

def Factor.Alg {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} (F : Factor D D') : Prop :=
  (∃ b : ℕ, 0 < b ∧ Star.star F.e * F.e = b • (Star.star F.e * F.f * F.e)) ∧
    Star.star F.e * F.f * F.e = Star.star F.e * Star.star F.f * F.e ∧ ∃ g : F.O, g * (Star.star F.e * F.f * F.e) = F.e

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.FormalEnd
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum

variable {R : Type} [CommRing R] [IsDomain R]

def EndData (D : DegPre R) (a a' : D.P.A ⟶ D.P.A) (h h' : D.X →+ D.X) : Prop :=
  IsMonHom a ∧ IsMonHom a' ∧ RosatiAdj D.P.A D.P.L a a' ∧ (∀ y, D.c (h y) = D.c y ≫ a) ∧ (∀ y, D.c (h' y) = D.c y ≫ a') ∧
    D.TauBal a a' h h'

variable {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

def FormalEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X)
    (b : ∀ e : ℕ, thickObj R I e G ⟶ thickObj R I e G) : Prop :=
  (∀ e, IsMonHom (b e)) ∧ (∀ e, thickMap R I e G ≫ (b (e + 1)).left = (b e).left ≫ thickMap R I e G) ∧
    (∀ e, b e ≫ (U.gt e).q = (U.gt e).q ≫ (Over.pullback (thick R I e)).map a) ∧
    ∀ e, ∃ t : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X,
      TorusEndOf D.toPre.X h' t ∧ (U.gt e).i ≫ b e = t ≫ (U.gt e).i

def LinEnd (U : UnifPre I D A G) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h' : D.toPre.X →+ D.toPre.X) (b : G ⟶ G) : Prop :=
  IsMonHom b ∧ FormalEnd U a h' fun e => (Over.pullback (thick R I e)).map b

def ExtLam (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB ((Over.pullback (jK R)).obj G).left)
    (PP : LB (G2 G).left) : Prop :=
  PP.IsLB ∧ ∀ κ₂ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
    Geo.Tor.IsSquare (G' := (Over.pullback (jK R)).obj G) (G := G) (pullback.fst G.hom (jK R)) κ₂ →
      LBIso (abelian₂ ((Over.pullback (jK R)).obj G) L) (PP.pull κ₂)

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsCharZero
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

abbrev RootFn (X : Over (Sp R)) (D : Type) [CommRing D] [Algebra R D] : Type 1 :=
  ∀ (D' : Type) [CommRing D'] [Algebra R D'], (D →ₐ[R] D') → Pt X D' → D'

variable {A : Over (Sp R)} [GrpObj A]


def HasRoots (A : Over (Sp R)) [GrpObj A] (n : ℕ) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), ∃ (D' : Type) (_ : CommRing D') (_ : Algebra R D')
    (ψ : D →ₐ[R] D') (z : Pt A D'), (ψ : D →+* D').FaithfullyFlat ∧ (z ^ n : Pt A D') = spOver ψ ≫ x

def IsTorsChar (n : ℕ) (b : Fn0 A) : Prop :=
  (∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (w : Pt A D),
    w ^ n = 1 → b D' (spOver φ ≫ w) = φ (b D w)) ∧
  ∀ (D : Type) [CommRing D] [Algebra R D] (w w' : Pt A D), w ^ n = 1 → w' ^ n = 1 → b D (w * w') = b D w + b D w'

def IsSec (n : ℕ) (b : Fn0 A) {D : Type} [CommRing D] [Algebra R D] (x : Pt A D) (s : RootFn A D) : Prop :=
  (∀ (D' : Type) [CommRing D'] [Algebra R D'] (D'' : Type) [CommRing D''] [Algebra R D''] (φ : D →ₐ[R] D')
    (ψ : D' →ₐ[R] D'') (z : Pt A D'), z ^ n = spOver φ ≫ x → s D'' (ψ.comp φ) (spOver ψ ≫ z) = ψ (s D' φ z)) ∧
  ∀ (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (z w : Pt A D'),
    z ^ n = spOver φ ≫ x → w ^ n = 1 → s D' φ (z * w) = s D' φ z + b D' w

abbrev SecFam (X : Over (Sp R)) : Type 1 := ∀ (D : Type) [CommRing D] [Algebra R D], Pt X D → RootFn X D

def IsSecDiff (n : ℕ) (S : SecFam A) (u : Fn1 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D)
    (E : Type) [CommRing E] [Algebra R E] (ψ : D' →ₐ[R] E) (z : Pt A E), z ^ n = spOver ψ ≫ spOver φ ≫ x →
    ψ (u D D' φ x) = S D' (spOver φ ≫ x) E ψ z - S D x E (ψ.comp φ) z

def IsSecAdd (n : ℕ) (S : SecFam A) (g : Fn2 A) : Prop :=
  ∀ (D : Type) [CommRing D] [Algebra R D] (x y : Pt A D) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E)
    (z w : Pt A E), z ^ n = spOver ψ ≫ x → w ^ n = spOver ψ ≫ y →
    ψ (g D x y) = S D (x * y) E ψ (z * w) - S D x E ψ z - S D y E ψ w


variable (R) in
def diagSum (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) : D ⊗[R] D →ₗ[R] D :=
  ∑ i ∈ Finset.range m, (Algebra.TensorProduct.lift (mulBy R D i : D →ₐ[R] D) (AlgHom.id R D)
    fun _ _ ↦ Commute.all _ _).toLinearMap

theorem diagSum_tmul (D : Type) [CommRing D] [Bialgebra R D] [Coalgebra.IsCocomm R D] (m : ℕ) (a b : D) :
    diagSum R D m (a ⊗ₜ b) = ∑ i ∈ Finset.range m, mulBy R D i a * b := by
  simp [diagSum, LinearMap.sum_apply]

end GlobalTheory.PtExt
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
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

def MinAt5 (F : SFam g n (zetaAway n)) {Z : Scheme.{0}} (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) : Prop :=
  ∃ (o' : Type) (_ : CommRing o') (β : cycAway n →+* o') (S' : Scheme.{0}) (s' : S' ⟶ Sp o') (U : S'.Opens)
    (c : U.toScheme ⟶ F.X) (π : S' ⟶ Z) (G : Over S') (_ : GrpObj G) (e : pullback F.univ.A.hom c ⟶ G.left)
    (_ : IsCommMonObj G) (N : ℕ),
    (IsThetaCompact F z i ∧ IsProjOver z ∧ IsNormalScheme Z ∧ i ≫ z = F.s ∧ Dense (Set.range i) ∧ OZ.IsLB ∧ IsAmpleLB OZ) ∧
    (β.Finite ∧ Function.Injective β ∧ IsProjOver s' ∧ IsNormalScheme S' ∧ Dense (U : Set S') ∧ IsFinite c ∧
      Surjective c ∧ U.ι ≫ π = c ≫ i ∧ π ≫ z = s' ≫ spMap β ∧ Surjective π ∧ IsProper π ∧
      IsNoetherian Z) ∧
    (IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
      IsGrpPullback ((Over.pullback c).obj F.univ.A) G U.ι e) ∧
    (1 ≤ N ∧ LBIso (OZ.pull π) (lbPow (hodge G g) N))

theorem MinAt5.isThetaCompact {F : SFam g n (zetaAway n)} {Z : Scheme.{0}} {z : Z ⟶ Sp (cycAway n)} {i : F.X ⟶ Z} {OZ : LB Z}
    (h : MinAt5 F z i OZ) : IsThetaCompact F z i ∧ OZ.IsLB ∧ IsAmpleLB OZ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, ⟨h₁, -, -, -, -, h₂, h₃⟩, -⟩ := h
  exact ⟨h₁, h₂, h₃⟩

def MinSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ n : ℕ, 3 ≤ n → Odd n → ∀ F : SFam g n (zetaAway n),
    ∃ (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z), MinAt5 F z i OZ

def ChartSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, IsPolFan id g φ → NoSelfInt id g φ → ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (OZ : LB Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      MinAt5 F z i OZ → BlowAt F z i φ d π j BD →
      SmoothOfRelativeDimension (g * (g + 1) / 2) (π ≫ z) ∧ ∀ x : S, PreChart F (π ≫ z) j φ BD d x

def DescSt5 : Prop :=
  ∀ g : ℕ, 1 ≤ g → ∀ φ : InvFun ℤ, ∀ n : ℕ, 3 ≤ n → Odd n →
    ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n)) (i : F.X ⟶ Z) (d : ℕ)
      (S : Scheme.{0}) (π : S ⟶ Z) (j : F.X ⟶ S) [IsOpenImmersion j] (BD : EffCartierData S),
      BlowAt F z i φ d π j BD → (∀ x : S, PreChart F (π ≫ z) j φ BD d x) →
      ∃ (G : Over S) (_ : GrpObj G) (e : F.univ.A.left ⟶ G.left), IsSemiAbelian G ∧ SmoothOfRelativeDimension g G.hom ∧
        IsGrpPullback F.univ.A G j e ∧ abLocus G = Set.range j

end GlobalTheory.SiegJoin
end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt

variable {R : Type} [CommRing R]

def Fn1.pull {X Y : Over (Sp R)} (q : Y ⟶ X) (u : Fn1 X) : Fn1 Y := fun D _ _ D' _ _ φ y ↦ u D D' φ (y ≫ q)

section Alg

variable {D E E' : Type} [CommRing D] [Algebra R D] [CommRing E] [Algebra R E] [CommRing E'] [Algebra R E']

def ptAlg (z : Pt (SpAlg R D) E) : D →ₐ[R] E :=
  { (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left).hom with
    commutes' := fun r ↦ by
      have h : CommRingCat.ofHom (algebraMap R D) ≫
          Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left =
          CommRingCat.ofHom (algebraMap R E) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage]
        exact Over.w z
      exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) h }

theorem spOver_ptAlg (z : Pt (SpAlg R D) E) : spOver (ptAlg z) = z := by
  apply Over.OverMorphism.ext
  rw [spOver_left]
  exact Spec.map_preimage (R := CommRingCat.of D) (S := CommRingCat.of E) z.left

theorem ptAlg_spOver (α : D →ₐ[R] E) : ptAlg (spOver α) = α := by
  refine AlgHom.ext fun r ↦ ?_
  change (Spec.preimage (R := CommRingCat.of D) (S := CommRingCat.of E) (spOver α).left).hom r = α r
  rw [spOver_left]
  exact congrArg (fun f ↦ CommRingCat.Hom.hom f r) (Spec.preimage_map (CommRingCat.ofHom (α : D →+* E)))

theorem ptAlg_comp (ψ : E →ₐ[R] E') (z : Pt (SpAlg R D) E) : ptAlg (spOver ψ ≫ z) = ψ.comp (ptAlg z) := by
  conv_lhs => rw [← spOver_ptAlg z, spOver_comp]
  exact ptAlg_spOver _

def epsEv (e : Pt (epsR R) E) : DualNumber E →ₐ[R] E :=
  DualNumber.lift ⟨(AlgHom.id R E, ptAlg (D := DualNumber R) e DualNumber.eps), by
    rw [← map_mul, DualNumber.eps_mul_eps, map_zero], fun _ ↦ Commute.all _ _⟩

end Alg

section Param

variable {A B : Over (Sp R)} {J : Type} [Fintype J] {D : Type} [CommRing D] [Algebra R D]

def sumMul (d : J → D) (b : J → Fn1 B) : Fn1 (SpAlg R D ⊗ B) := fun E _ _ E' _ _ ψ z ↦
  ∑ i, ψ (ptAlg (z ≫ fst _ _) (d i)) * b i E E' ψ (z ≫ snd _ _)

def IsCupCob {K : Type} (W : K → (A ⊗ B).left.Opens) (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) : Prop :=
  ∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (E'' : Type) [CommRing E'']
    [Algebra R E''] (φ : E →ₐ[R] E') (ψ : E' →ₐ[R] E'') (z : Pt (A ⊗ B) E), Sm W z →
    ψ (n E E' φ z) - n E E'' (ψ.comp φ) z + n E' E'' ψ (spOver φ ≫ z) =
      ∑ i, ψ (a i E E' φ (z ≫ fst _ _)) * b i E' E'' ψ (spOver φ ≫ z ≫ snd _ _)

def parCoc (a : J → Fn1 A) (b : J → Fn1 B) (n : Fn1 (A ⊗ B)) (x : Pt A D) : Fn1 (SpAlg R D ⊗ B) :=
  fun E _ _ E' _ _ ψ z ↦ n E E' ψ (z ≫ x ▷ B) -
    ∑ i, ψ (a i D E (ptAlg (z ≫ fst _ _)) x) * b i E E' ψ (z ≫ snd _ _)

def parCov {K : Type} (W : K → (A ⊗ B).left.Opens) (x : Pt A D) : K → (SpAlg R D ⊗ B).left.Opens :=
  fun i ↦ (x ▷ B).left ⁻¹ᵁ W i

end Param

section Change

variable {R' : Type} [CommRing R'] (σ : R →+* R')

@[reducible] def algVia (E : Type) [CommRing E] [Algebra R' E] : Algebra R E :=
  ((algebraMap R' E).comp σ).toAlgebra

def homVia {E E' : Type} [CommRing E] [Algebra R' E] [CommRing E'] [Algebra R' E'] (ψ : E →ₐ[R'] E') :
    @AlgHom R E E' _ _ _ (algVia σ E) (algVia σ E') :=
  @AlgHom.mk R E E' _ _ _ (algVia σ E) (algVia σ E') (ψ : E →+* E') fun r ↦ ψ.commutes (σ r)

variable {σ} {X : Over (Sp R)} {X' : Over (Sp R')} {q : X'.left ⟶ X.left}

def ptVia (w : q ≫ X.hom = X'.hom ≫ spMap σ) {E : Type} [CommRing E] [Algebra R' E] (y : Pt X' E) :
    @Pt R _ X E _ (algVia σ E) :=
  Over.homMk (y.left ≫ q) (by
    have h : y.left ≫ X'.hom = spMap (algebraMap R' E) := Over.w y
    change (y.left ≫ q) ≫ X.hom = spMap ((algebraMap R' E).comp σ)
    rw [Category.assoc, w, ← Category.assoc, h, Cris.spMap_comp])

def bcPull (w : q ≫ X.hom = X'.hom ≫ spMap σ) (u : Fn1 X) : Fn1 X' := fun E _ _ E' _ _ ψ y ↦
  @u E _ (algVia σ E) E' _ (algVia σ E') (homVia σ ψ) (ptVia w y)

end Change

section Gen

variable {X Y : Over (Sp R)}

def IsPtGen (L : LB X.left) (q : Y ⟶ X)
    (t : ∀ (E : Type) [CommRing E] [Algebra R E], Pt Y E → L.ι → E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → IsUnit (t E z i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (z : Pt Y E)
    (i : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i → t E' (spOver ψ ≫ z) i = ψ (t E z i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (z : Pt Y E) (i j : L.ι), ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U i →
    ⊤ ≤ (z ≫ q).left ⁻¹ᵁ L.U j → t E z i = evU (z ≫ q).left (L.U i ⊓ L.U j) (L.g i j).val * t E z j

variable {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

def IsEpsGen (P : LB (A ⊗ B).left) (v : epsR R ⟶ B)
    (T : ∀ (E : Type) [CommRing E] [Algebra R E], Pt A E → P.ι → DualNumber E) : Prop :=
  (∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → IsUnit (T E x i)) ∧
  (∀ (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : E →ₐ[R] E') (x : Pt A E)
    (i : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i → T E' (spOver ψ ≫ x) i = epsHom ψ (T E x i)) ∧
  ∀ (E : Type) [CommRing E] [Algebra R E] (x : Pt A E) (i j : P.ι), ⊤ ≤ x.left ⁻¹ᵁ chartsA P i →
    ⊤ ≤ x.left ⁻¹ᵁ chartsA P j → T E x i = evU (ptV v x).left (P.U i ⊓ P.U j) (P.g i j).val * T E x j

end Gen

end GlobalTheory.PtExt
end
end

