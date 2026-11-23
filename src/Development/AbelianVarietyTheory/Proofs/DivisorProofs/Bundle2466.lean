module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2385
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0063
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1799
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsLocalRingTrivSqZeroExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemChart
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1323
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1416
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2324
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1373
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2328
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsLeadOfUnif
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2312
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2296
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2395
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2386
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2390
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2375
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitive
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NearOpenSumEqEmbeddingDescendedMultiplication
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

theorem toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    Desc.toS N p hp ≫ pullback.snd _ _ = pullback.snd _ _ ≫ p := pullback.lift_snd _ _ _

theorem embL_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.fst G.hom p = Desc.toS N p hp ≫ N.u := pullback.lift_fst _ _ _

theorem embL_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    (Desc.emb N p hp).left ≫ pullback.snd G.hom p = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem pairU_fst' (N : Near π G) :
    pairU N ≫ (fst N.U N.U).left = (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ fst _ _).left = _
  rw [lift_fst]; rfl

theorem pairU_snd' (N : Near π G) :
    pairU N ≫ (snd N.U N.U).left = (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ := by
  show (lift (fstU N) (sndU N) ≫ snd _ _).left = _
  rw [lift_snd]; rfl

theorem fst_hom' (N : Near π G) :
    (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (fst (Desc.UT N) (Desc.UT N))

theorem snd_hom' (N : Near π G) :
    (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.snd N.U.hom (pullback.fst π π ≫ π) = (Desc.UT N ⊗ Desc.UT N).hom :=
  Over.w (snd (Desc.UT N) (Desc.UT N))

theorem mT_fst' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) : mT N V m hm ≫ pullback.fst _ _ = (pairU N ∣_ V) ≫ m :=
  pullback.lift_fst _ _ _

theorem mT_snd' (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left)
    (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom) :
    mT N V m hm ≫ pullback.snd _ _ = (VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

variable {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}

theorem fst_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem snd_toS_fst' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.fst _ _ =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ pullback.fst _ _ :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_fst' N p hp))

theorem fst_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (fst_hom' N))))

theorem snd_toS_snd' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ pullback.snd _ _ = (Desc.UT N ⊗ Desc.UT N).hom ≫ p :=
  (Category.assoc _ _ _).trans ((congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (toS_snd' N p hp)).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (snd_hom' N))))

theorem fst_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (fst (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((fst (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

theorem snd_toS_u' (N : Near π G) (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π) :
    ((snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp) ≫ N.u =
      (snd (Desc.UT N) (Desc.UT N)).left ≫ (Desc.emb N p hp).left ≫ pullback.fst G.hom p :=
  (Category.assoc _ _ _).trans (congrArg ((snd (Desc.UT N) (Desc.UT N)).left ≫ ·) (embL_fst' N p hp).symm)

end GlobalTheory.Mum.DescKP

namespace GlobalTheory.Mum.DescKP

theorem sum_eq_mT_emb : ∀ {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G] (N : Near π G) (V : (N.U ⊗ N.U).left.Opens) (m : V.toScheme ⟶ N.U.left) (hm : m ≫ N.U.hom = V.ι ≫ (N.U ⊗ N.U).hom), (∀ (T : Scheme.{0}) (v : T ⟶ V.toScheme) (s : T ⟶ S) (x y : Over.mk s ⟶ G), N.Pt s (v ≫ V.ι ≫ (fst N.U N.U).left) x.left → N.Pt s (v ≫ V.ι ≫ (snd N.U N.U).left) y.left → N.Pt s (v ≫ m) (x * y).left) → ∀ (p : pullback π π ⟶ S) (hp : p ≫ π = pullback.fst π π ≫ π), (DescKP.VT N V).ι ≫ (Desc.sum N p hp).left = DescKP.mT N V m hm ≫ (Desc.emb N p hp).left := by
  intro R _ _ S π G _ N V m hm law p hp
  let T0 : Over (pullback π π) := Over.mk ((VT N V).ι ≫ (Desc.UT N ⊗ Desc.UT N).hom)
  let ι0 : T0 ⟶ Desc.UT N ⊗ Desc.UT N := Over.homMk (VT N V).ι rfl
  let a : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ fst _ _ ≫ Desc.emb N p hp
  let b : T0 ⟶ (Over.pullback p).obj G := ι0 ≫ snd _ _ ≫ Desc.emb N p hp
  have hab : ι0 ≫ Desc.sum N p hp = a * b := by rw [Desc.sum, comp_mul]
  have wpt : ∀ c : T0 ⟶ (Over.pullback p).obj G, (c.left ≫ pullback.fst G.hom p) ≫ G.hom = T0.hom ≫ p := by
    intro c
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    exact congrArg (· ≫ p) (Over.w c)
  let x : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (a.left ≫ pullback.fst G.hom p) (wpt a)
  let y : Over.mk (T0.hom ≫ p) ⟶ G := Over.homMk (b.left ≫ pullback.fst G.hom p) (wpt b)
  have hxy : (x * y).left = (a * b).left ≫ pullback.fst G.hom p :=
    (isGrpPullback_pullback G p).2 T0 a b x y rfl rfl
  have e : (pairU N ∣_ V) ≫ V.ι = (VT N V).ι ≫ pairU N := morphismRestrict_ι _ _
  have e' : ∀ {Z : Scheme.{0}} (h : (N.U ⊗ N.U).left ⟶ Z), (pairU N ∣_ V) ≫ V.ι ≫ h = (VT N V).ι ≫ pairU N ≫ h :=
    fun h => by rw [← Category.assoc, e, Category.assoc]
  have ptx : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (fst N.U N.U).left) x.left := by
    refine ⟨(VT N V).ι ≫ (fst (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((fst_toS_fst' N p hp).trans (pairU_fst' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (fst_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  have pty : N.Pt (T0.hom ≫ p) ((pairU N ∣_ V) ≫ V.ι ≫ (snd N.U N.U).left) y.left := by
    refine ⟨(VT N V).ι ≫ (snd (Desc.UT N) (Desc.UT N)).left ≫ Desc.toS N p hp, ?_, ?_, ?_⟩
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) ((snd_toS_fst' N p hp).trans (pairU_snd' N).symm)).trans (e' _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_snd' N p hp)).trans (Category.assoc _ _ _).symm)
    · exact (Category.assoc _ _ _).trans ((congrArg ((VT N V).ι ≫ ·) (snd_toS_u' N p hp)).trans (Category.assoc _ _ _).symm)
  obtain ⟨x₀, h₁, h₂, h₃⟩ := law (VT N V).toScheme (pairU N ∣_ V) (T0.hom ≫ p) x y ptx pty
  have hx₀ : x₀ = mT N V m hm ≫ Desc.toS N p hp := by
    apply pullback.hom_ext
    · exact h₁.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_fst' N p hp)).trans (mT_fst' N V m hm))).symm)
    · exact h₂.trans (((Category.assoc _ _ _).trans ((congrArg (mT N V m hm ≫ ·) (toS_snd' N p hp)).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ p) (mT_snd' N V m hm))))).symm)
  apply pullback.hom_ext
  · rw [Category.assoc (mT N V m hm), embL_fst']
    refine (?_ : _ = (mT N V m hm ≫ Desc.toS N p hp) ≫ N.u).trans (Category.assoc _ _ _)
    rw [← hx₀, h₃, hxy, ← hab]
    rfl
  · have w : (Desc.sum N p hp).left ≫ pullback.snd G.hom p = (Desc.UT N ⊗ Desc.UT N).hom := Over.w _
    rw [Category.assoc, w, Category.assoc, embL_snd', mT_snd']

end GlobalTheory.Mum.DescKP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NefOfSemipositiveFibrewise
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Filter Topology
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.Cartier
  GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal
open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CechPic
open GlobalTheory.LB (toMod)
open GlobalTheory.VB (degOfRank)

namespace GlobalTheory.NefGeneric

theorem ratDeg_nonneg : ∀ (k : Type) [CommRing k] (W : Scheme.{0}) (q : W ⟶ Sp k) (L : HermLB q),
    IsArithVar q 1 → ArInt.NefFib L → 0 ≤ ratDeg q L.B := by
  intro k _ W q L hW hL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e1, e2⟩ := GlobalTheory.T.eulerChar_lineBundle_fibre_modp_eq_rat_projective k W q 1 hW 2 L.B L.isLB
  obtain ⟨hproj, hdim⟩ := GlobalTheory.T.arithmeticSurface_fibre_isProjOver_zmod_dim_le_one k W q hW 2
  letI := GlobalTheory.algebraΓOfHom
    (pullback.snd (q ≫ spMap (Int.castRingHom k)) (spMap (Int.castRingHom (ZMod 2))))
  have h := GlobalTheory.T.degree_nonneg_of_curveDegree_nonneg_over_zmod 2 _ hproj hdim _ (LB.isLB_pull L.isLB _)
    (fun Z i _ _ _ hZ => GlobalTheory.T.curveDegree_nonneg_zmodFibre_of_nefOnFiniteFieldFibres k W q L 2 hL Z i hZ)
  rw [ratDeg, degOfRank, ← e1, ← e2]
  simpa [degOfRank] using h

end GlobalTheory.NefGeneric

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumMult

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D : DegData R (maximalIdeal R)}
  {A : PolAV (Sp (FractionRing R))} {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]

abbrev multW (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (e : ℕ)
    (i i' : Fin 1 → U.LG.L.ι) : (thickObj R (maximalIdeal R) e G).left.Opens :=
  ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i ⊓
    (fstG (maximalIdeal R) e G).left ⁻¹ᵁ secChart U.LG.L i'

def MultAct (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G) (N : ℕ)
    (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, multW U b e i i')) :
    Prop :=
  ∀ k : ℕ, 3 ≤ k → ∀ (f : IntFam (maximalIdeal R) D.toPre k) (s : H0 U.LG.L k), (∀ e, U.ExpandsAt e k s f.f) →
    ∃ F : IntFam (maximalIdeal R) D.toPre (N * k), ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι),
      ChartExpOn U.toUnifPre e (N * k) i' (multW U b e i i')
        (m e i i' ^ k * ((thickObj R (maximalIdeal R) e G).left.presheaf.map
          (homOfLE (inf_le_left : multW U b e i i' ≤
            ((b e).left ≫ (fstG (maximalIdeal R) e G).left) ⁻¹ᵁ secChart U.LG.L i)).op).hom
          ((((b e).left ≫ (fstG (maximalIdeal R) e G).left).app (secChart U.LG.L i)).hom (s.f i))) F.f

def LeadPt (U : Unif (maximalIdeal R) D A G)
    (b : ∀ e : ℕ, thickObj R (maximalIdeal R) e G ⟶ thickObj R (maximalIdeal R) e G)
    (m : ∀ (e : ℕ) (i i' : Fin 1 → U.LG.L.ι), Γ((thickObj R (maximalIdeal R) e G).left, multW U b e i i')) :
    Prop :=
  ∃ x : D.toPre.P.A.left, D.toPre.P.A.hom x = (IsLocalRing.closedPoint R : PrimeSpectrum R) ∧
    ∀ y : (thickObj R (maximalIdeal R) 0 G).left, (U.gt 0).pG.left y = x →
      ∀ i i' : Fin 1 → U.LG.L.ι, y ∈ multW U b 0 i i' →
        y ∈ (thickObj R (maximalIdeal R) 0 G).left.basicOpen (m 0 i i')

def PosN (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X) (N : ℕ) :
    Prop :=
  RelAmple D.toPre.P.A (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]) ∧
    ∀ (κ : D.toPre.X → (FractionRing R)ˣ), (∀ y, κ (-y) = κ y) → κ 0 = 1 →
      (∀ x y z, κ (x + y + z) * κ x * κ y * κ z = κ (x + y) * κ (x + z) * κ (y + z)) →
      (∀ y, ∃ r : R, (κ y : FractionRing R) = algebraMap R _ r) →
      (∀ y z, ∃ u : Rˣ, ((κ (h y + z) * κ y * κ (h' z) : (FractionRing R)ˣ) : FractionRing R) =
        algebraMap R _ (u : R) * ((κ (y + h' z) * κ (h y) * κ z : (FractionRing R)ˣ) : FractionRing R)) →
      ∀ y, ∃ r : R, ((κ y ^ N : (FractionRing R)ˣ) : FractionRing R) = algebraMap R _ r * κ y * κ (h y)

def NonzeroAt (D : DegData R (maximalIdeal R)) (a : D.toPre.P.A ⟶ D.toPre.P.A) (N : ℕ)
    (σ₀ : LB.Sec (LB.LinComb D.toPre.P.L (K := Fin 2) ![𝟙 D.toPre.P.A.left, a.left] ![(N : ℤ), -1]))
    (x : D.toPre.P.A.left) : Prop :=
  ∀ j : Fin 2 → D.toPre.P.L.ι,
    x ∈ LB.wchart D.toPre.P.L (![𝟙 D.toPre.P.A.left, a.left] : Fin 2 → (D.toPre.P.A.left ⟶ D.toPre.P.A.left)) j →
      x ∈ D.toPre.P.A.left.basicOpen (σ₀.f j)

end GlobalTheory.MumMult
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NzEverywhere
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin

theorem nz_everywhere {S : Scheme.{0}} (G : Over S) [GrpObj G] [Smooth G.hom] (L : LB G.left) {R : Type} [CommRing R]
    [IsLocalRing R] (χ : Sp R ⟶ S) (σ : LB.Sec (LPow G L ((1 : ℕ) : ℤ) (Over.mk χ))) (h : NZ G L χ σ) :
    ∀ y : (Over.mk χ).left, ∃ g, (fst (Over.mk χ) G).left g = y ∧ g ∈ nonzeroLocus σ := by
  obtain ⟨x, hc, hx⟩ := h
  haveI : Smooth (fst (Over.mk χ) G).left := by
    change Smooth (pullback.fst χ G.hom)
    infer_instance
  have ho : IsOpen ((fst (Over.mk χ) G).left '' (nonzeroLocus σ : Set _)) :=
    (fst (Over.mk χ) G).left.isOpenMap _ (nonzeroLocus σ).isOpen
  intro y
  obtain ⟨g, hg, e⟩ := (IsLocalRing.specializes_closedPoint (R := R) y).mem_open ho ⟨x, hx, hc⟩
  exact ⟨g, e, hg⟩

theorem nz_pull : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left), L.IsLB → IsSemiAbelian G →
    ∀ (R V : Type) [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V] (χ : Sp R ⟶ S) (σ : SecAt G L χ)
      (φ : R →+* V), NZ G L χ σ → NZ G L (spMap φ ≫ χ) (SecAt.pull G L σ φ) := by
  intro S G _ L hL hG R V _ _ _ _ χ σ φ h
  haveI : Smooth G.hom := hG.smooth
  exact nz_pullS G hL σ (nz_everywhere G L χ σ h) (spMap φ ≫ χ) _

end GlobalTheory.UMin
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfTwistedAdjointComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam

namespace GlobalTheory.MumFam


open AdjComp in
theorem Adj.of_twisted_comp : ∀ (R : Type) [CommRing R] [IsDomain R] (Q₁ Q₂ : Data R) (a : Q₁.B ⟶ Q₂.B) (a₁ a₁' : Q₁.B ⟶ Q₁.B) (a' : Q₂.B ⟶ Q₁.B) (h : Q₁.X →+ Q₂.X) (h₁ h₁' : Q₁.X →+ Q₁.X) (h' : Q₂.X →+ Q₁.X), IsMonHom a → IsMonHom a' → (∀ y, Q₂.c (h y) = Q₁.c y ≫ a) → (∀ z, Q₁.c (h' z) = Q₂.c z ≫ a') → Adj Q₁ Q₁ a₁ a₁' h₁ h₁' → (∃ w : LB.Iso (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L) (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L), w.IsGen ∧ ∀ y y' z J₁ J₂, Good Q₁.M.L z J₁ → Good Q₂.M.L z J₂ → val (Q₂.tau (h y) y') (𝟙 _) z J₂ = adjVal w (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left z J₁ J₂ * val (Q₁.tau (h₁ y) (h' y')) (𝟙 _) z J₁) → Adj Q₁ Q₂ a (a' ≫ a₁') h (h₁'.comp h') := by
  intro R _ _ Q₁ Q₂ a a₁ a₁' a' h h₁ h₁' h' ma ma' ca ca' H₁ H₂
  obtain ⟨mb, mb', cb, cb', w₁, g₁, V₁⟩ := H₁
  obtain ⟨w₂, g₂, V₂⟩ := H₂
  let m₂ : Q₁.B ⊗ Q₂.B ⟶ Q₁.B ⊗ Q₁.B := lift (fst _ _) (snd _ _ ≫ a')
  have xB : ∀ i, (![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B ≫ a₁, snd Q₁.B Q₁.B] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  have xC : ∀ i, (![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] : Fin 2 → _) i = m₂ ≫ (![fst Q₁.B Q₁.B, snd Q₁.B Q₁.B ≫ a₁'] : Fin 2 → _) i := by
    intro i; fin_cases i <;> simp [m₂]
  let cB := cubePull Q₁.M.L m₂ _ _ xB
  let cC := cubePull Q₁.M.L m₂ _ _ xC
  have lA : (cubeLB Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] Q₂.M.L).IsLB := DVR.linComb_isLB _ Q₂.M.isLB _ _
  have lB : (cubeLB Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  have lC : (cubeLB Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] Q₁.M.L).IsLB := DVR.linComb_isLB _ Q₁.M.isLB _ _
  obtain ⟨w, gw, hw⟩ := exists_comp lA lB lC w₂ g₂ (pullIso cB cC w₁) (pullIso_isGen cB cC g₁)
  refine ⟨ma, inferInstance, ca, fun y => ?_, w, gw, fun y y' z J₁ J₂ hJ₁ hJ₂ => ?_⟩
  · rw [AddMonoidHom.comp_apply, cb', ca', Category.assoc]
  · have e₂ := V₂ y y' z J₁ J₂ hJ₁ hJ₂
    have e₁ := V₁ y (h' y') z J₁ J₁ hJ₁ hJ₁
    have hP : (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₁.c (h' y'))).left =
        (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left ≫ m₂.left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc, ca', Category.assoc]
    rw [hP] at e₁
    generalize (lift (toUnit (TK R) ≫ Q₁.c y) (toUnit (TK R) ≫ Q₂.c y')).left = P at e₂ e₁ ⊢
    have mC := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B, snd Q₁.B Q₂.B ≫ a' ≫ a₁'] I.down).left) P
    have mB := Good.mem hJ₁ (fun I : ULift (Finset (Fin 2)) => (psum Q₁.B ![fst Q₁.B Q₂.B ≫ a₁, snd Q₁.B Q₂.B ≫ a'] I.down).left) P
    have mA := Good.mem hJ₂ (fun I : ULift (Finset (Fin 2)) => (psum Q₂.B ![fst Q₁.B Q₂.B ≫ a, snd Q₁.B Q₂.B] I.down).left) P
    have K : adjVal w P z J₁ J₂ = adjVal w₂ P z J₁ J₂ * adjVal w₁ (P ≫ m₂.left) z J₁ J₁ := by
      refine ((adjVal_of w P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).trans ((hw _ P z _ _ _ mC mB mA).trans
        (congrArg₂ (· * ·) (gm_pullIso cB cC w₁ P z (_, _) ⟨mC, mB⟩) rfl))).trans ?_
      rw [mul_comm]
      refine congrArg₂ (· * ·) (adjVal_of w₂ P z J₁ J₂ _ _ (fun _ => rfl) (fun _ => rfl)).symm
        (adjVal_of w₁ (P ≫ m₂.left) z J₁ J₁ _ _ (fun I => ?_) (fun I => ?_)).symm
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xC I]
      · show J₁ _ = J₁ _
        rw [Category.assoc, ← psum_left_pull m₂ _ _ xB I]
    rw [AddMonoidHom.comp_apply, e₂, e₁, K]
    exact (_root_.mul_assoc _ _ _).symm

end GlobalTheory.MumFam
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrigVal
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.Mum

def OrigVal {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {k : ℕ} {α : D.X} (b : D.SecB k α) (v : R) : Prop :=
  ∀ (z : Sp R) (J : (Sp R ⟶ D.P.A.left) → D.P.L.ι), Good D.P.L z J →
    sval b (unitW D.P.A) z J = stalkOf z v * (val D.rig (idW R) z J).val ^ k

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingKernelTrivial
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

theorem GlobalTheory.Mum.pairing_kernel_trivial : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (_ : F.Alg) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)] := by
  intro R _ _ _ hR D D' F hF A' G' _ _ hG' U' oA oG hlin G _ _ hG inc pr hinc hpr hip hpi κ₀ hκ T x hx
  have h1 := GlobalTheory.T.pull_generator_factor_pairing_generic_mumfordBundle R D D' F A' G' U' oA oG hlin G inc hinc κ₀ hκ T x hx
  have hra : (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) ≫ ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) = oA.act F.e := by
    have e1 := hlin.ext F.e
    rw [← hpi, CategoryTheory.Functor.map_comp] at e1
    rw [Category.assoc, ← Category.assoc ((Over.pullback (jK R)).map pr), e1, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have h2 := GlobalTheory.T.rosati_star_mul_kills_point_of_trivial_pairing (FractionRing R) A' F.O oA F.e F.f ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).map inc ≫ U'.gen.hom) (U'.gen.inv ≫ (Over.pullback (jK R)).map pr) hra T (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) h1
  have hip' : (Over.pullback (jK R)).map inc ≫ (Over.pullback (jK R)).map pr = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, hip, CategoryTheory.Functor.map_id]
  have he : (x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom) ≫ oA.act F.e = x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom := by
    rw [← hra]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc ((Over.pullback (jK R)).map inc) ((Over.pullback (jK R)).map pr), hip', Category.id_comp]
  obtain ⟨-, hsym, g, hg⟩ := hF
  set y := x ≫ (Over.pullback (jK R)).map inc ≫ U'.gen.hom with hy
  have hu : y ≫ oA.act (Star.star F.e * F.f * F.e) = toUnit T ≫ η[A'.A] := by
    rw [hsym, oA.map_mul, ← Category.assoc, he, h2]
  have h3 : y = toUnit T ≫ η[A'.A] := by
    have : IsMonHom (oA.act g) := oA.hom g
    rw [← he, ← hg, oA.map_mul, ← Category.assoc, hu, Category.assoc, IsMonHom.one_hom]
  have hx' : x = y ≫ U'.gen.inv ≫ (Over.pullback (jK R)).map pr := by
    rw [hy]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hip', Category.comp_id]
  rw [hx', h3]
  have hη : η[A'.A] ≫ U'.gen.inv = η[(Over.pullback (jK R)).obj G'] := by
    have : IsMonHom U'.gen.hom := U'.gen_hom
    rw [← IsMonHom.one_hom U'.gen.hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have : IsMonHom ((Over.pullback (jK R)).map pr) := inferInstance
  rw [Category.assoc, ← Category.assoc η[A'.A], hη, IsMonHom.one_hom]
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialSumCompMonHomEqPartialSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.MumProd.PsumMap

theorem psum_comp_hom : ∀ (S : Scheme.{0}) (B B₁ T : Over S) [GrpObj B] [IsCommMonObj B] [GrpObj B₁] [IsCommMonObj B₁] (n : ℕ) (p : B ⟶ B₁) (x : Fin n → (T ⟶ B)) (x₁ : Fin n → (T ⟶ B₁)), IsMonHom p → (∀ i, x i ≫ p = x₁ i) → ∀ I : Finset (Fin n), psum B x I ≫ p = psum B₁ x₁ I := by
  intro S B B₁ T _ _ _ _ n p x x₁ hp hx I
  unfold psum
  induction ((List.finRange n).filter (· ∈ I)) with
  | nil =>
    show (toUnit T ≫ η[B]) ≫ p = toUnit T ≫ η[B₁]
    rw [Category.assoc, IsMonHom.one_hom]
  | cons a l ih =>
    rw [List.foldr_cons, List.foldr_cons, ← ih]
    show (lift (x a) _ ≫ μ[B]) ≫ p = lift (x₁ a) _ ≫ μ[B₁]
    rw [Category.assoc, IsMonHom.mul_hom, ← Category.assoc, lift_map, hx a]

end GlobalTheory.MumProd.PsumMap
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelFamilySimilitudeGroupActionFreeTransitiveStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegelFamily_similitudeGroup_action_free_transitive : ∀ (h n N : ℕ) (F : SFam h N (zetaAway N)) (j : cycAway n →+* cycAway N), 3 ≤ n → Odd N → n ∣ N → j (zetaAway n) = zetaAway N ^ (N / n) → ∃ (Ga : Type) (_ : Group Ga) (_ : Finite Ga) (ρ : Ga → (F.X ⟶ F.X)) (ν : Ga → (F.univ.A.left ⟶ F.univ.A.left)), ρ 1 = 𝟙 _ ∧ (∀ a c, ρ (a * c) = ρ a ≫ ρ c) ∧ ν 1 = 𝟙 _ ∧ (∀ a c, ν (a * c) = ν a ≫ ν c) ∧ (∀ a, ρ a ≫ F.s ≫ spMap j = F.s ≫ spMap j) ∧ (∀ a, SRelBy F.univ F.univ (N / n) (N / n) (ρ a) (ν a)) ∧ (∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ F.X) (a : Ga), y ≫ ρ a = y → a = 1) ∧ ∀ (R : Type) [CommRing R] [IsLocalRing R] (y y' : Sp R ⟶ F.X) (s' : Sp R ⟶ Sp (cycAway n)) (c : SiegPre h n (zetaAway n) s'), y ≫ F.s ≫ spMap j = y' ≫ F.s ≫ spMap j → SRel c F.univ 1 (N / n) y → SRel c F.univ 1 (N / n) y' → ∃ a, y ≫ ρ a = y' := by
  first | exact @GlobalTheory.SiegAct.siegel_group_action | exact GlobalTheory.SiegAct.siegel_group_action | (intros; apply GlobalTheory.SiegAct.siegel_group_action <;> assumption)
end

