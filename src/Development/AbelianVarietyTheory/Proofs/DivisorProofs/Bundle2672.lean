module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasThetaConstantsTwoLevelsMoveCartesian
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2484
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryModuliFinitePointsWithGivenPolarisedFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2524
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2432
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2229
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2179
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapInverseNatCast
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0141
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBoxGenOfSection
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2492
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1161
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0031

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapCoordsOfSymmetricThetaIsomorphicFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem pCrd_of_symAt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o : Type) [CommRing o] (X : Scheme.{0}) (q : X ⟶ S) (f : X ⟶ PSpace o n) (S' : Scheme.{0}) (A : Over S') [GrpObj A] [IsCommMonObj A] (L' : LB A.left) (ρ' : LB.Gen (L'.pull (eSec A))) (Ω : Type) [Field Ω] [CharZero Ω] (x : Sp Ω ⟶ X) (x' : Sp Ω ⟶ S') (P : PolAV (Sp Ω)) (α : P.A.left ⟶ G.left) (α' : P.A.left ⟶ A.left) (θ : SecAt A L' x') (e : Fin (n + 1) → Ω), Odd m → n + 1 = m ^ (4 * g) → ThMap G L ρ m q f → L'.IsLB → ρ'.IsGen → P.g = g → IsGrpPullback P.A G (x ≫ q) α → LBIso P.L (L.pull α) → IsGrpPullback P.A A x' α' → LBIso P.L (L'.pull α') → IsGenSec A L' _ θ → SymAt A L' ρ' m x' θ e → PCrd (x ≫ f) e := by
  intro S G _ _ L ρ hL hρ g m n o _ X q f S' A _ _ L' ρ' Ω _ _ x x' P α α' θ e hm hn hf hL' hρ' hg hα hw hα' hw' hθ he
  have hpol : PolFib A L' g x' := ⟨P, α', hg, hα', hw'⟩
  obtain ⟨Ω', _, _, pt, c, -, -, -, hl, -⟩ := _root_.GlobalTheory.UMin.GalTh.thList_galois S' A L' ρ' hL' hρ' g m (n + 1) Ω x' θ hm hn hpol
  have hgen := (_root_.GlobalTheory.UMin.gen_of_polFib S' A L' hL' g Ω x' hpol).2 θ hθ Ω' (algebraMap Ω Ω')
  have h₁ : HasTh₂ A L' ρ' m m (spMap (algebraMap Ω Ω') ≫ x') c c := hasTh_iff.1 ⟨_, pt, hgen, hl⟩
  obtain ⟨w, hw₀⟩ := id hw
  obtain ⟨ρP, hρP, -⟩ := exists_rigidificationPullbackCompatibleIso hα hw₀ hL P.isLB hρ
  haveI : IsCommMonObj P.A := P.isAb.comm
  have h₂ := (_root_.GlobalTheory.UMin.ThMove.hasTh₂_move S' A L' ρ' hL' hρ' _ P.A P.L ρP x' α' P.isLB hρP hα' hw' m m _ _ Ω' _ c c).2 h₁
  have h₃ := (_root_.GlobalTheory.UMin.ThMove.hasTh₂_move S G L ρ hL hρ _ P.A P.L ρP (x ≫ q) α P.isLB hρP hα hw m m _ _ Ω' _ c c).1 h₂
  rw [← Category.assoc] at h₃
  have h₄ := hf Ω' _ c (hasTh_iff.2 h₃)
  refine _root_.GlobalTheory.UMin.CrdUniq.main.2.2 o Ω Ω' n _ e (algebraMap Ω Ω') ?_
  rw [← Category.assoc, funext (he Ω' _ pt c hl)]
  exact h₄

end GlobalTheory.UMin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaMapFiniteGeometricFibresOfLargeLevel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.QF

theorem polFib_transport {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {K : Type}
    [Field K] {x : Sp K ⟶ S} {P P' : PolAV (Sp K)} (φ : P'.A ≅ P.A) (hφ : IsPolIso P' P φ)
    {α : P.A.left ⟶ G.left} (hα : IsGrpPullback P.A G x α) (hLα : LBIso P.L (L.pull α)) :
    IsGrpPullback P'.A G x (φ.hom.left ≫ α) ∧ LBIso P'.L (L.pull (φ.hom.left ≫ α)) := by
  have := hφ.1
  refine ⟨((ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_of_iso φ).comp hα).congr (Category.id_comp _) rfl, ?_⟩
  obtain ⟨t, ht⟩ := hφ.2
  have h1 : LBIso P'.L (P.L.pull φ.hom.left) := LBIso.symm ⟨t, ht⟩
  have h2 : LBIso (P.L.pull φ.hom.left) (L.pull (φ.hom.left ≫ α)) :=
    LBIso.chartPull (chartPullPull P.L φ.hom.left)
      (chartPullSame L (fun _ : PUnit => φ.hom.left ≫ α) (fun _ => α) (fun _ => 1) φ.hom.left
        (fun _ => rfl)) hLα
  exact LBIso.trans P'.isLB (pull_isLB P.isLB _) (pull_isLB hL _) h1 h2

theorem charZero_of_pt {F K : Type} [Field F] [CharZero F] [Field K] (t : Sp K ⟶ Sp F) : CharZero K := by
  have f := (Spec.preimage t).hom
  exact (f.charZero_iff f.injective).1 inferInstance

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def ThetaData (Xo : Moduli Dw l) {K : Type} [Field K] (y : Sp K ⟶ Xo.X) (g m : ℕ) (ze : Γ(Sp K, ⊤)ˣ)
    (v : (Fin (2 * g) → ZMod (m ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) : Prop :=
  ∃ (P : PolAV (Sp K)) (hg : P.g = g) (α : P.A.left ⟶ Xo.univ.t.G.left) (lev : Out.Level P (m ^ 2) ze),
    IsGrpPullback P.A Xo.univ.t.G y α ∧ LBIso P.L (Xo.univ.t.PP.L.pull α) ∧ IsThetaPt P m (levelPoint lev hg) v

theorem finite_thetaData (Xo : Moduli Dw l) (c : Coeff l) (g j : ℕ) (hbig : 81 ^ g * g.factorial < 3 ^ j * 81)
    (K : Type) [Field K] [IsAlgClosed K] (h3 : ((3 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ) (x : Sp K ⟶ Xo.XF c)
    (v : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Γ((baseOver (Sp K)).left, ⊤)) :
    Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze v} := by
  by_cases hne : ∃ y₀ : Sp K ⟶ Xo.XF c, y₀ ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧
      ThetaData Xo (y₀ ≫ pullback.fst _ _) g (3 ^ j * 81) ze v
  · obtain ⟨y₀, -, P₀, hg₀, -, lev₀, -, -, hθ₀⟩ := hne
    have hQ := _root_.GlobalTheory.UMinQF.finite_points E H Dw l Xo K P₀ (x ≫ pullback.fst _ _ ≫ Xo.s)
    refine Set.Finite.of_finite_image (f := fun y => y ≫ pullback.fst _ _) (hQ.subset ?_) ?_
    · rintro _ ⟨y, ⟨hys, P, hg, α, lev, hpb, hPL, hθ⟩, rfl⟩
      refine ⟨?_, ?_⟩
      · show (y ≫ pullback.fst _ _) ≫ Xo.s = x ≫ pullback.fst _ _ ≫ Xo.s
        rw [Category.assoc, pullback.condition, ← Category.assoc, hys, Category.assoc, ← pullback.condition]
      · obtain ⟨φ, hφ, -⟩ := (_root_.GlobalTheory.thetaPtDetermines_and_endDeterminedOnTorsion).1 g 3 2 j 81 (3 ^ j * 81) Nat.prime_three (by decide) le_rfl
          (by norm_num) rfl hbig K h3 P₀ P hg₀ hg ze lev₀ lev v hθ₀ hθ
        exact ⟨φ.hom.left ≫ α, polFib_transport Xo.univ.t.PP.isLB φ hφ hpb hPL⟩
    · intro y₁ h₁ y₂ h₂ h
      exact pullback.hom_ext h (h₁.1.trans h₂.1.symm)
  · apply Set.Finite.subset Set.finite_empty
    intro y hy
    exact False.elim (hne ⟨y, hy⟩)

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

theorem exists_thetaData (Xo : Moduli Dw l) (c : Coeff l) {o : Type} [CommRing o] {n j g : ℕ}
    (hg : g = Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) (f : Xo.XF c ⟶ PSpace o n)
    (hn : n + 1 = (3 ^ j * 81) ^ (4 * g))
    (hth : ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f)
    (K : Type) [Field K] [IsAlgClosed K] (hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0) (ze : Γ(Sp K, ⊤)ˣ)
    (hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2)) (x : Sp K ⟶ Xo.XF c) (e : Fin (n + 1) → K)
    (he : PCrd (x ≫ f) e) (T : Finset (Fin (n + 1) → K))
    (hT : ∀ (c : Fin (n + 1) → K) (a : K), a ≠ 0 → (∀ j, symTup c j = a * e j) →
      ∃ mu : K, mu ≠ 0 ∧ (fun b => mu * c b) ∈ T)
    (y : Sp K ⟶ Xo.XF c) (hy : y ≫ f = x ≫ f) :
    ∃ (t : T) (β : (Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)),
      ThetaData Xo (y ≫ pullback.fst _ _) g (3 ^ j * 81) ze (fun a => GlobalTheory.ZH.fn ((t : Fin (n + 1) → K) (β a))) := by
  have hodd : Odd (3 ^ j * 81) := (Odd.pow (by decide : Odd 3)).mul (by decide : Odd 81)
  have hLB := Xo.univ.t.PP.isLB
  have hρ := Xo.univ.t.PP.rigGen
  obtain ⟨P, α, hPg, hpb, hPL⟩ := _root_.GlobalTheory.UMin.polFib_univ E H Dw l Xo c K (y ≫ pullback.fst _ _)
  rw [← hg] at hPg
  have hfib : PolFib Xo.univ.t.G Xo.univ.t.PP.L g (y ≫ pullback.fst _ _) := ⟨P, α, hPg, hpb, hPL⟩
  obtain ⟨⟨θ, hθ⟩, -⟩ := _root_.GlobalTheory.UMin.gen_of_polFib _ Xo.univ.t.G Xo.univ.t.PP.L hLB g K _ hfib
  obtain ⟨pt, cy, hcy⟩ := _root_.GlobalTheory.UMin.exists_thList _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ g (3 ^ j * 81) (n + 1) K
    _ θ hodd hm0 hn hfib
  have hH : HasTh Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (y ≫ pullback.fst _ _) cy :=
    ⟨θ, pt, hθ, hcy⟩
  have hP1 : PCrd (y ≫ f) (symTup cy) := hth K y cy hH
  rw [hy] at hP1
  obtain ⟨a, ha0, ha⟩ := (_root_.GlobalTheory.UMin.CrdUniq.main).2.1 o K n (x ≫ f) e (symTup cy) he hP1
  obtain ⟨mu, hmu0, hmuT⟩ := hT cy a ha0 ha
  haveI := P.isAb.comm
  obtain ⟨rig, hrig⟩ := P.rigid
  have hP : HasTh P.A P.L rig (3 ^ j * 81) (𝟙 (Sp K)) cy := by
    rw [hasTh_iff] at hH ⊢
    refine (_root_.GlobalTheory.UMin.ThMove.hasTh₂_move _ Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig hLB hρ (Sp K) P.A P.L rig
      (y ≫ pullback.fst _ _) α P.isLB hrig hpb hPL (3 ^ j * 81) (3 ^ j * 81) (n + 1) (n + 1) K (𝟙 _) cy cy).2 ?_
    rwa [Category.id_comp]
  obtain ⟨lev, β, hβ⟩ := _root_.GlobalTheory.UMin.exists_level_isThetaPt_of_hasTh K P rig g (3 ^ j * 81) (n + 1) hPg cy ze hrig hodd hm0 hze hP
  exact ⟨⟨_, hmuT⟩, β, P, hPg, α, lev, hpb, hPL, hβ mu hmu0⟩

end GlobalTheory.UMin.QF

namespace GlobalTheory.UMin.QF

theorem finite_fibre_thMap : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (o : Type) [CommRing o] (j n : ℕ) (f : Xo.XF c ⟶ PSpace o n), 81 ^ (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)) * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q)).factorial < 3 ^ j * 81 → n + 1 = (3 ^ j * 81) ^ (4 * (Module.finrank ℚ E / 2 * (Dw.p + Dw.q))) → ThMap Xo.univ.t.G Xo.univ.t.PP.L Xo.univ.t.PP.rig (3 ^ j * 81) (pullback.fst _ _ : Xo.XF c ⟶ Xo.X) f → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ Xo.XF c), Set.Finite {y : Sp K ⟶ Xo.XF c | y ≫ pullback.snd _ _ = x ≫ pullback.snd _ _ ∧ y ≫ f = x ≫ f} := by
  intro E _ _ _ H Dw l Xo c o _ j n f hbig hn hth K _ _ x
  haveI : CharZero K := charZero_of_pt (x ≫ pullback.snd _ _)
  set g := Module.finrank ℚ E / 2 * (Dw.p + Dw.q) with hg
  have hm0 : ((3 ^ j * 81 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by positivity)
  have h3 : ((3 : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.2 (by norm_num)
  have hpos : 0 < (3 ^ j * 81) ^ 2 := by positivity
  haveI : NeZero (((3 ^ j * 81) ^ 2 : ℕ) : K) := ⟨Nat.cast_ne_zero.2 hpos.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K ((3 ^ j * 81) ^ 2)
  let eK := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hz' := hz.map_of_injective eK.injective
  set ze : Γ(Sp K, ⊤)ˣ := (hz'.isUnit hpos.ne').unit with hzedef
  have hze : IsPrimitiveRoot ze ((3 ^ j * 81) ^ 2) := hz'.isUnit_unit hpos.ne'
  obtain ⟨⟨e, he⟩, -⟩ := (_root_.GlobalTheory.UMin.CrdBasic.pCrd_basic).2.2 o K n (x ≫ f)
  obtain ⟨T, hT⟩ := _root_.GlobalTheory.UMin.symTup_scale_finite K (n + 1) e
  haveI : NeZero ((3 ^ j * 81) ^ 2) := ⟨hpos.ne'⟩
  refine (Set.finite_iUnion fun d : T × ((Fin (2 * g) → ZMod ((3 ^ j * 81) ^ 2)) → Fin (n + 1)) =>
    finite_thetaData Xo c g j hbig K h3 ze x
      (fun a => GlobalTheory.ZH.fn ((d.1 : Fin (n + 1) → K) (d.2 a)))).subset ?_
  rintro y ⟨h1, h2⟩
  obtain ⟨t, β, hd⟩ := exists_thetaData Xo c hg f hn hth K hm0 ze hze x e he T hT y h2
  exact Set.mem_iUnion.2 ⟨(t, β), h1, hd⟩

end GlobalTheory.UMin.QF
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomain
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UMin.SymRing

theorem exists_common_field : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁], Module.FaithfullyFlat R R₁ → ∀ (K : Type) [Field K] (i : R →+* K), ∃ (K' : Type) (_ : Field K') (φ : K →+* K') (i₁ : R₁ →+* K'), i₁.comp (algebraMap R R₁) = φ.comp i := by
  intro R R₁ _ _ _ hff K _ i
  letI : Algebra R K := i.toAlgebra
  haveI : Nontrivial (K ⊗[R] R₁) := Module.FaithfullyFlat.rTensor_nontrivial R R₁ K
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R] R₁)
  letI : Field ((K ⊗[R] R₁) ⧸ M) := Ideal.Quotient.field M
  refine ⟨(K ⊗[R] R₁) ⧸ M, inferInstance,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := R₁)).toRingHom,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := R₁)).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgHom.commutes, show i r = algebraMap R K r from rfl, AlgHom.commutes]

theorem symTup_map' {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun a => i (c a)) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [symTup, Finset.esymm_map_val, map_pow, map_sum, map_prod]

theorem symTup_perm' {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  funext j
  show _ = (Finset.univ.val.map c).esymm _ ^ _
  rw [symTup, ← Function.comp_def c σ, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem sym_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → R, SymAt G L ρ m x θ e := by
  intro S G _ _ L ρ hL hρ g m N R _ _ _ _ _ x θ hm hmu hN hP
  obtain ⟨R₁, _, _, c, hfin, hff, hc⟩ := _root_.GlobalTheory.UMin.thList_cover S G L ρ hL hρ g m N R x θ hm hmu hN hP
  have hP' : ∀ j, ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) →
      i₁ (symTup c j) = i₂ (symTup c j) := by
    intro j K _ i₁ i₂ h
    obtain ⟨pt₁, h₁⟩ := hc K (i₁.comp (algebraMap R R₁)) i₁ rfl
    obtain ⟨pt₂, h₂⟩ := hc K (i₁.comp (algebraMap R R₁)) i₂ h.symm
    obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.UMin.SymCmp.thList_ext_perm S G L ρ hL hρ g m R x θ hm hmu hP K K _ _ (RingHom.id K) (RingHom.id_comp _) N pt₁ _ pt₂ _ h₁ h₂
    rw [symTup_map', symTup_map', funext hσ]
    exact (symTup_perm' (fun b => i₁ (c b)) σ).symm ▸ rfl
  choose e he using fun j => _root_.GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq R R₁ hfin hff (symTup c j) (hP' j)
  refine ⟨e, fun K _ i pt c' hl j => ?_⟩
  obtain ⟨K', _, φ, i₁, hφ⟩ := exists_common_field R R₁ hff K i
  obtain ⟨pt₁, h₁⟩ := hc K' (φ.comp i) i₁ hφ
  obtain ⟨σ, hσ⟩ := _root_.GlobalTheory.UMin.SymCmp.thList_ext_perm S G L ρ hL hρ g m R x θ hm hmu hP K K' i (φ.comp i) φ rfl N pt c' pt₁ _ hl h₁
  apply φ.injective
  have h1 : φ (i (e j)) = i₁ (algebraMap R R₁ (e j)) := by rw [← RingHom.comp_apply, ← RingHom.comp_apply, hφ]
  rw [h1, ← he j K' i₁, symTup_map', symTup_map', funext hσ]
  exact congrFun (symTup_perm' (fun a => φ (c' a)) σ) j

end GlobalTheory.UMin.SymRing

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTranslateValuesShiftByRootOfUnity
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.UPoinc.USum

theorem uSame_self {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} (ρ : S.Real) :
    USame ρ ρ (fun b => b) (RingHom.id Ω) := by
  let f := spMap S.R.val.toRingHom
  let P := ρ.P
  let P₀ : PolAV (Sp Ω) := {
    A := (Over.pullback f).obj P.A
    isAb := TLinPf.isAb_pullback f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (isGrpPullback_pullback P.A f).1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := pull_isLB P.isLB _
    rigid := GlobalTheory.PolBaseChange.rigidified_pull (isGrpPullback_pullback P.A f) P.rigid
    sym := GlobalTheory.PolBaseChange.sym_pull (isGrpPullback_pullback P.A f) P.sym
    ample := by
      letI := P.isAb.proper
      exact GlobalTheory.AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample (IsPullback.of_hasPullback P.A.hom f)
    ktriv := by
      obtain ⟨w, hw⟩ := GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB P.isLB (pullback.fst P.A.hom f))
      exact kTriv_pull (isGrpPullback_pullback P.A f) P.isLB (pull_isLB P.isLB _) ((isGen_iff w).1 hw) P.ktriv }
  refine ⟨P₀, pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom), pullback.fst ρ.P.A.hom (spMap S.R.val.toRingHom),
    isGrpPullback_pullback _ _, isGrpPullback_pullback _ _, GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB,
    GlobalTheory.PolBaseChange.lbIso_refl P₀.isLB, fun b => ?_⟩
  refine ⟨pullback.lift (spMap S.R.val.toRingHom ≫ (ρ.pt b).left) (𝟙 _) ?_, pullback.lift_fst _ _ _,
    pullback.lift_fst _ _ _⟩
  rw [Category.assoc, Over.w]; simp [f]

theorem sum_ev_shift : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] {S : ThetaSys o Ω}
    (ρ : S.Real) (H : AddSubgroup S.Gam) (m : ℕ), S.N = m ^ 2 → ∀ h h' : S.Gam, m • h = m • h' → h' - h ∈ H →
    ∃ ξ : Ω, (∃ k : ℕ, 0 < k ∧ ξ ^ k = 1) ∧ ∀ t ∈ S.perp H,
      ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h' j = ξ * ∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j := by
  intro o Ω _ _ _ _ S ρ H m hm h h' e hH
  obtain ⟨P₀, a, a', x, hx, hadd⟩ := exists_isGenLab (uSame_self ρ)
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨ξ₁, ⟨k₁, hk₁, hξ₁⟩, hc₁⟩ :=
    _root_.GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h rfl
  obtain ⟨ξ₂, ⟨k₂, hk₂, hξ₂⟩, hc₂⟩ :=
    _root_.GlobalTheory.UPoinc.TwCompare.twVal_eq_root_mul ρ ρ (fun b => b) (RingHom.id Ω) P₀ a a' x hx m hm (m • h) x₀ h' e.symm
  have hξ₂0 : ξ₂ ≠ 0 := by
    rintro rfl
    rw [zero_pow hk₂.ne'] at hξ₂
    exact zero_ne_one hξ₂
  refine ⟨ξ₁ * ξ₂⁻¹, ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩, fun t ht => ?_⟩
  · rw [mul_pow, inv_pow, pow_mul, hξ₁, one_pow, mul_comm k₁, pow_mul, hξ₂, one_pow, inv_one, mul_one]
  obtain ⟨v, hv⟩ := TV.ex hx hadd hm t (h := h) (κ := m • h) rfl
  have hv' := hv.transl hx hadd hm (k := h' - h) (by rw [smul_sub, e, sub_self]) (ht _ hH)
  rw [add_sub_cancel] at hv'
  have E₁ := hc₁ t v hv
  have E₂ := hc₂ t v hv'
  simp only [RingHom.id_apply] at E₁ E₂
  have E := E₂.symm.trans E₁
  have hinv : ξ₂ * ξ₂⁻¹ = 1 := mul_inv_cancel₀ hξ₂0
  rw [← sub_eq_zero]
  refine (mul_eq_zero.1 ?_).resolve_left (mul_ne_zero hξ₂0 hx₀)
  linear_combination E - ξ₁ * S.th x₀ * (∑ j, algebraMap o Ω (S.ρ t j ρ.i₀) * S.ev h j) * hinv

end GlobalTheory.UPoinc.USum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
namespace GlobalTheory.ProdUnif

open GlobalTheory.WCub GlobalTheory.PowUnif


set_option maxHeartbeats 1600000 in
theorem cubAlong_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (D : DegData R I) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → ∀ (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (L : LB (G₁ ⊗ G₂).left) (c : CubGen (G₁ ⊗ G₂) L) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A)) (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) wM (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t → IsBoxGen (φ₁ := thφ G₁ (x3 G₁)) (φ₂ := thφ G₂ (x3 G₂)) wL (fst G₁ G₂ ⊗ₘ fst G₁ G₂ ⊗ₘ fst G₁ G₂).left (snd G₁ G₂ ⊗ₘ snd G₁ G₂ ⊗ₘ snd G₁ G₂).left c U₁.cubG.t U₂.cubG.t → ∀ (e : ℕ) (g : GtCoord I D.toPre e (G₁ ⊗ G₂)), g.pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left → g.pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left → ∀ w : LB.Iso (L.pull (fstG I e (G₁ ⊗ G₂)).left) (D.toPre.P.L.pull g.pG.left), BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left) (T₂ := (thickObj R I e G₂).left) wM wL w (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left → CubAlong I D.toPre e (G₁ ⊗ G₂) L c g.pG w := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D p₁ p₂ q₁ q₂ hS wM L c wL hLB hM hL e g h₁ h₂ w hQ T x jL jM cL cM
  have := g.q_hom
  have := (U₁.gt e).q_hom
  have := (U₂.gt e).q_hom
  have := hS.hom₁
  have := hS.hom₂
  refine (clause_iff (tri (thick R I e) g.pG x) (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x)
    (fun k : thK => (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left) _ _ _ (D.toPre.cub.t.s jM) (c.s jL)
    (fun k => w.s (fun _ => jM k, fun _ => jL k)) thε).2 fun y hB hG' _ => ?_
  obtain ⟨J, hJ, eJ⟩ := exists_good D.toPre.P.L D.toPre.P.isLB y _ jM cM (fun k => Set.mem_iInter.1 hB k)
  obtain ⟨N, hN, eN⟩ := exists_good L hLB y _ jL cL (fun k => Set.mem_iInter.1 hG' k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.toPre.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.toPre.P.isLB y
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at U₁.LG.isLB y
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at U₂.LG.isLB y
  have tM₁ := (tri_map (thick R I e) (U₁.gt e).pG g.pG x _ p₁ h₁).2
  have tM₂ := (tri_map (thick R I e) (U₂.gt e).pG g.pG x _ p₂ h₂).2
  have tL₁ := (tri_map (thick R I e) (fstG I e G₁) (fstG I e (G₁ ⊗ G₂)) x _ (fst G₁ G₂)
    (thick_fstG I e (fst G₁ G₂))).2
  have tL₂ := (tri_map (thick R I e) (fstG I e G₂) (fstG I e (G₁ ⊗ G₂)) x _ (snd G₁ G₂)
    (thick_fstG I e (snd G₁ G₂))).2
  have bM := hM T.left (tri (thick R I e) g.pG x) y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [tM₁, tM₂] at bM
  have bL := hL T.left (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x) y N₁ N₂ N hN₁ hN₂ hN
  rw [tL₁, tL₂] at bL
  have v₁ := w_cub_val.{0} U₁ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) y hJ₁ hN₁
  have v₂ := w_cub_val.{0} U₂ e T (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) y hJ₂ hN₂

  have fM := fun k : thK => tri_thφ (thick R I e) g.pG x g.q rfl k
  have fG := fun k : thK => tri_thφ (thick R I e) (fstG I e (G₁ ⊗ G₂)) x (𝟙 _) (Category.id_comp _).symm k
  have fM₁ := fun k : thK => tri_thφ (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (U₁.gt e).q rfl k
  have fM₂ := fun k : thK => tri_thφ (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (U₂.gt e).q rfl k
  have fG₁ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have fG₂ := fun k : thK => tri_thφ (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) (𝟙 _)
    (Category.id_comp _).symm k
  have ps₁ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down
  have ps₂ := fun k : thK => psum_comp x ((Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down
  have key := rel_alg thε
    (fun k => om wM y J₁ J₂ J (tri (thick R I e) g.pG x ≫ thφ D.toPre.P.A (x3 D.toPre.P.A) k))
    (fun k => om wL y N₁ N₂ N (tri (thick R I e) (fstG I e (G₁ ⊗ G₂)) x ≫ thφ (G₁ ⊗ G₂) (x3 (G₁ ⊗ G₂)) k))
    (fun k => gw w (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y (jM k) (fun _ => jL k))
    (fun k => gw (U₁.w e) (psum (thickObj R I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) k.down).left y
      (J₁ (tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k))
      (fun _ => N₁ (tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k)))
    (fun k => gw (U₂.w e) (psum (thickObj R I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) k.down).left y
      (J₂ (tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k))
      (fun _ => N₂ (tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k)))
    (fun k => by
      have q := hQ T.left (psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left y J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      have a₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₁.left =
          tri (thick R I e) (U₁.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ D₁.toPre.P.A (x3 D₁.toPre.P.A) k := by
        rw [Category.assoc, h₁, ← Category.assoc, ps₁ k, fM₁ k]
      have a₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ g.pG.left) ≫ p₂.left =
          tri (thick R I e) (U₂.gt e).pG (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ D₂.toPre.P.A (x3 D₂.toPre.P.A) k := by
        rw [Category.assoc, h₂, ← Category.assoc, ps₂ k, fM₂ k]
      have b₁ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (fst G₁ G₂).left =
          tri (thick R I e) (fstG I e G₁) (fun a => x a ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂)) ≫ thφ G₁ (x3 G₁) k := by
        rw [Category.assoc, thick_fstG I e (fst G₁ G₂), ← Category.assoc, ps₁ k, fG₁ k]
      have b₂ : ((psum (thickObj R I e (G₁ ⊗ G₂)) x k.down).left ≫ (fstG I e (G₁ ⊗ G₂)).left) ≫ (snd G₁ G₂).left =
          tri (thick R I e) (fstG I e G₂) (fun a => x a ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂)) ≫ thφ G₂ (x3 G₂) k := by
        rw [Category.assoc, thick_fstG I e (snd G₁ G₂), ← Category.assoc, ps₂ k, fG₂ k]
      rw [a₁, a₂, b₁, b₂, ps₁ k, ps₂ k, ← fM k, ← fG k, eJ k, eN k] at q
      exact q)
    bM bL v₁ v₂
  refine (val_of _ _ y J jM eJ).symm.trans (key.trans ?_)
  exact congrArg _ (val_of c _ y N jL eN)

end GlobalTheory.ProdUnif
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopChernDensityHolomorphicChartEtale
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem topDens_holoChart : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → (Real.pi ^ X.dim)⁻¹ * (mixTop fun _ => curvAt (fun v => H A (e.symm v) ()) (e y)).re = ‖transDet e c.e y‖ ^ 2 * topDens E H c y := by
  intro F _ σ X m E O H hM e he c y hy hye hyc A hA
  set G : V X.dim → Matrix (Fin m) (Fin m) ℂ := fun u => H A (c.e.symm u) () with hG
  set φ : V X.dim → V X.dim := c.e ∘ e.symm with hφ
  have ho := isOpen_over e c.e.open_source
  have hm := mem_over e hye hyc
  have hdiff : DifferentiableOn ℂ φ (e.target ∩ e.symm ⁻¹' c.e.source) := holoChart_trans_algChart he c
  have han : AnalyticAt ℂ φ (e y) := GlobalTheory.InjHol.analyticAt_of_differentiableOn_euclidean ho hm hdiff
  have hφy : φ (e y) = c.e y := by simp only [hφ, Function.comp_apply, e.left_inv hye]
  have hG2 : MContDiffAt 2 G (φ (e y)) := hφy ▸ hM.mContDiffAt_chart hy c hyc hA ()
  have hGu : IsUnit (G (φ (e y))).det := hφy ▸ hM.isUnit_det_chart hy c hyc hA ()
  have hger : (fun v => H A (e.symm v) ()) =ᶠ[𝓝 (e y)] fun v => G (φ v) := by
    filter_upwards [ho.mem_nhds hm] with w hw
    simp only [hG, hφ, Function.comp_apply, c.e.left_inv hw.2]
  have hcurv : curvAt (fun v => H A (e.symm v) ()) (e y) = curvAt (fun v => G (φ v)) (e y) := by
    funext a b
    exact curv_congr hger _ _
  have key := _root_.GlobalTheory.GoodTop.mixTop_curvAt_comp_holo (G := G) (φ := φ) (w := e y) (han.contDiffAt) hG2 hGu
  rw [hcurv, key, hφy]
  have hfr : topDens E H c y = chernTop (MvPolynomial.X ((), X.dim)) (fun v => H A (c.e.symm v)) (c.e y) :=
    hM.chernTop_frame _ hy c hyc (E.nonempty (under y)).choose_spec hA
  rw [hfr, _root_.GlobalTheory.GoodTop.chernTop_eq_mixTop, transDet, Complex.re_ofReal_mul]
  ring

end GlobalTheory.GoodTop
end

