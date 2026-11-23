module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothHermCombLine
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.ArakelovSingularities.IsClosedImmersionLift
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0527
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarFundamentalDomainOrthogonalSum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DeRhamJacobian.IsdRJ
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0206
public import Development.WeilBound.CoreStatements.PlaceConnectedComponents.IsOpenQuotientMapArt0
public import GroundTheory.LocalFields.Bundle0016
public import GroundTheory.LocalFields.KroneckerWeber
public import GroundTheory.PAdicHodge.FieldOfNormsCyclBase
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0666
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0335
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0465
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0469
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0483
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0475
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0468
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0467
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0534
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0538
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DualIsConjByOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1068
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
public import GroundTheory.AutomorphicForms.FiniteLengthJacquet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0960
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.LSegJacquet
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightEqOfFullIntersectionSystem
section
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace

open ReciprocityTheory.ChartRestriction.G.Geo (MRing IsMultiHomog HermLine IsSmoothHerm IsHorizontal divSupp multAt geoNum charOf ptsIntegral
  IsIntersectionFamily IntersectionSystem IsFullIntersectionSystem)
open ReciprocityTheory.ChartRestriction.G.AI.I2 (IsRatSectionOn logNormRat RatRStatement)
open GlobalTheory.CompanionTheory.MPDict

namespace GlobalTheory.CompanionTheory.MixZ

variable {m : ℕ} {n : Fin (m + 1) → ℕ}

theorem dim_of_generic {X Z : Scheme.{0}} [IsIntegral Z] (j : Z ⟶ X) [IsClosedImmersion j] :
    topologicalKrullDim (closure ({j (genericPoint Z)} : Set X)) = topologicalKrullDim Z := by
  have hrange : Set.range j = closure {j (genericPoint Z)} := by
    have h₁ := (genericPoint_spec Z).image j.continuous
    rw [Set.image_univ, j.isClosedEmbedding.isClosed_range.closure_eq] at h₁
    exact h₁.def.symm
  exact topologicalKrullDim_eq_of_isEmbedding j.isClosedEmbedding.isEmbedding hrange

theorem dim_closure_image {X Y : Scheme.{0}} (j : Y ⟶ X) [IsClosedImmersion j] (z : Y) :
    topologicalKrullDim (closure ({j z} : Set X)) = topologicalKrullDim (closure ({z} : Set Y)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  exact (dim_of_generic (k ≫ j)).trans (dim_of_generic k).symm

theorem isometric_restr_restr {X Z : Scheme.{0}} (N : HermLB (mpStr ℤ m n)) (i : X ⟶ MP ℤ m n) (j : Z ⟶ X) :
    ((N.restr i).restr j).Isometric (N.pull (j ≫ i) (Category.assoc _ _ _)) := by
  have hm : ∀ (c : ((N.restr i).restr j).B.ι) (x : Z), x ∈ ((N.restr i).restr j).B.U c →
      x ∈ (N.pull (j ≫ i) (Category.assoc _ _ _)).B.U (fun _ => c PUnit.unit PUnit.unit) := fun c x h =>
    (mem_pull (F := j ≫ i) (x := x)).2 ((mem_pull (F := i) (x := j x)).1 ((mem_pull (F := j) (x := x)).1 h))
  refine HermLB.isometric_of_chart (fun c _ => c PUnit.unit PUnit.unit) (fun c x h => hm c x h) (fun x c c' h h' => ?_)
    fun σ c y hy => ?_
  · have h₁ := (mem_pull (F := j) (x := x)).1 h
    have h₁' := (mem_pull (F := j) (x := x)).1 h'
    refine (gm_pull_g (N.B.pull i) j (𝟙 Z) x c c' h h').trans ?_
    refine (gm_pull_g N.B i (𝟙 Z ≫ j) x _ _ h₁ h₁').trans ?_
    refine Eq.trans ?_ (gm_pull_g N.B (j ≫ i) (𝟙 Z) x _ _ (hm c x h) (hm c' x h')).symm
    simp only [Category.assoc]
  · refine ((N.φ σ).pull_φ (j ≫ i) (Category.assoc _ _ _) _ y).trans ?_
    refine Eq.trans ?_ ((((N.φ σ).pull i rfl).pull_φ j rfl c y)).symm
    refine Eq.trans ?_ ((N.φ σ).pull_φ i rfl _ _).symm
    congr 1

theorem archInt_transport {Z : Scheme.{0}} [IsIntegral Z] {q : Z ⟶ Sp ℤ} {L M : HermLB q} (iso : L.Isometric M)
    {r : L.B.ι → Z.functionFieldˣ} (hr : IsRatSec L.B r) :
    ∃ (r' : M.B.ι → Z.functionFieldˣ) (hr' : IsRatSec M.B r'), M.div hr' = L.div hr ∧
      (∀ e, M.archInt M e hr' = L.archInt L e hr) ∧
      ∀ σ, Set.EqOn (GlobalTheory.Cartier.logNorm (M.φ σ) r') (GlobalTheory.Cartier.logNorm (L.φ σ) r) (GlobalTheory.Cartier.offSupp q σ (L.div hr)) := by
  obtain ⟨r', hr', h₁, h₂⟩ := iso.exists_isRatSec hr
  refine ⟨r', hr', h₁, fun e => ?_, h₂⟩
  simp only [HermLB.archInt, h₁, iso.chernInt_eq]
  exact finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (h₂ σ)

theorem rec_eq (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (e : ℕ) (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) e)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.restr i).archInt (N.restr i) e hr := by
  obtain ⟨f, g, hfg, hrat⟩ := h₅ m n N A hN Z i r hr
  have hcyc := h₆ m n N A hN Z i e hZ r hr f g hfg hrat (cycVal II A e)
  have hint := h₇ m n N N A A hN hN Z i e hZ hA hA r hr f g hfg hrat
  have hrr := hR _ _ (II _ (Bk n)) (hII.1 _ _) _ e (fun _ => A) A f g hP (fun _ => hA) hA hfg
  have hs : (Fin.snoc (fun _ : Fin e => A) A : Fin (e + 1) → HermLine (Bk n)) = fun _ => A := by
    funext j
    refine Fin.lastCases ?_ (fun j => ?_) j <;> simp
  rw [hs] at hrr
  rw [hint, hcyc, cycVal, if_pos hP.2.2.1, hrr]
  rfl

theorem mp_var (m : ℕ) (n : Fin (m + 1) → ℕ) : GlobalTheory.IsArithVar (mpStr ℤ m n) (∑ i, n i) :=
  GlobalTheory.Amb.isArithVar_mp ℤ inferInstance m n

theorem not_horizontal_of_dim_zero (h₃ : PtDict) {X : Scheme.{0}} (i : X ⟶ MP ℤ m n) [IsClosedImmersion i] (z : X)
    (hz : topologicalKrullDim (closure ({z} : Set X)) = (0 : ℕ)) : ¬ IsHorizontal (ptIdeal (i z)) := by
  obtain ⟨Z, k, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hd : topologicalKrullDim Z = (0 : ℕ) := (dim_of_generic k).symm.trans hz
  obtain ⟨-, h2, -, -⟩ := h₃ m n Z (k ≫ i) 0 hd
  intro hh
  have hc : CharZero Γ(Z, ⊤) := h2.1 hh
  exact (mp_var m n).dim_ne_zero (k ≫ i) hc (by exact_mod_cast hd)

theorem curve_eq (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] (hZ : GlobalTheory.IsArithVar (i ≫ mpStr ℤ m n) 0)
    (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.restr i).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.restr i).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.restr i).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts (i ≫ mpStr ℤ m n) σ, logNorm ((N.restr i).φ σ) r y := by
  rw [rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i 0 hZ hP r hr, (hC Z _ hZ (N.restr i) (N.restr i) r hr).2]
  refine congrArg (· - _) (finsum_congr fun z => ?_)
  by_cases hz : ((N.restr i).div hr).mult z = 0
  · simp [hz]
  have hd := h₄ Z _ 0 hZ z (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
  rw [cycVal, if_neg (not_horizontal_of_dim_zero h₃ i z hd), hPt m n Z i z hd]

theorem rec_eq' (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q) (e : ℕ)
    (hZ : GlobalTheory.IsArithVar q e) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) (e + 1))
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A (e + 1) (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * cycVal II A e (ptIdeal (i z)) -
        (N.pull i hq).archInt (N.pull i hq) e hr := by
  subst hq
  exact rec_eq h₅ h₆ h₇ hR II hII N A hN hA Z i e hZ hP r hr

theorem curve_eq' (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hPt : PtLen)
    (hC : CurveInt) (hR : RatRStatement)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) (N : HermLB (mpStr ℤ m n)) (A : HermLine (Bk n))
    (hN : IsHermRep N A) (hA : IsSmoothHerm A) (Z : Scheme.{0}) [IsIntegral Z] [IsLocallyNoetherian Z]
    (i : Z ⟶ MP ℤ m n) [IsClosedImmersion i] {q : Z ⟶ Sp ℤ} (hq : i ≫ mpStr ℤ m n = q)
    (hZ : GlobalTheory.IsArithVar q 0) (hP : Geo.IsArithVar (ptIdeal (i (genericPoint Z))) 1)
    (r : (N.pull i hq).B.ι → Z.functionFieldˣ) (hr : IsRatSec (N.pull i hq).B r) :
    cycVal II A 1 (ptIdeal (i (genericPoint Z))) =
      ∑ᶠ z, (((N.pull i hq).div hr).mult z : ℝ) * Real.log (Nat.card (Z.residueField z)) -
        ∑ᶠ σ, ∑ᶠ y : CxPts q σ, logNorm ((N.pull i hq).φ σ) r y := by
  subst hq
  exact curve_eq h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z i hZ hP r hr

theorem charP_of_cast {R : Type} [CommRing R] [IsDomain R] {p : ℕ} (hp : p.Prime) (h : (p : R) = 0) : CharP R p := by
  obtain ⟨ℓ, hℓ⟩ := CharP.exists R
  rcases (Nat.dvd_prime hp).1 ((CharP.cast_eq_zero_iff R ℓ p).1 h) with rfl | rfl
  · exact absurd ((Nat.cast_one (R := R)).symm.trans ((CharP.cast_eq_zero_iff R 1 1).2 dvd_rfl)) one_ne_zero
  · exact hℓ

theorem heightEq_of (h₃ : PtDict) (h₄ : CodimOne) (h₅ : ExistsRat) (h₆ : CycleOfRat) (h₇ : ArchIntEq) (hV : VertEq)
    (hPt : PtLen) (hC : CurveInt) (hR : RatRStatement) (II : IntersectionSystem) (hII : IsFullIntersectionSystem II) :
    HeightEq II := by
  intro m n N A hN hA X _ _ i _ h H z d hd
  induction d using Nat.strong_induction_on generalizing z with
  | _ d ih =>
  obtain ⟨Z, j, _, _, rfl⟩ := GlobalTheory.exists_isClosedImmersion_genericPoint z
  have hZd : topologicalKrullDim Z = d := (dim_of_generic j).symm.trans hd
  have hmp := mp_var m n
  have hnoeth := hmp.isNoetherian_sub (j ≫ i)
  have hln : IsLocallyNoetherian Z := hnoeth.toIsLocallyNoetherian
  have hcomp : ∀ x, (j ≫ i) x = i (j x) := fun x => by simp
  obtain ⟨-, hp₃, hp₄, hp₅⟩ := h₃ m n Z (j ≫ i) d hZd
  simp only [hcomp] at hp₃ hp₄ hp₅
  by_cases hW : IsHorizontal (ptIdeal (i (j (genericPoint Z))))
  · have hc : CharZero Γ(Z, ⊤) := hp₃.1 hW
    have hP := hp₄ hW
    obtain ⟨r₀, hr₀⟩ := exists_isRatSec ((N.restr i).restr j).isLB
    obtain ⟨r, hr, e₁, e₂, e₃⟩ := archInt_transport (isometric_restr_restr N i j) hr₀
    cases d with
    | zero => exact absurd (by exact_mod_cast hZd) (hmp.dim_ne_zero (j ≫ i) hc)
    | succ e =>
      have hZ₀ : GlobalTheory.IsArithVar ((j ≫ i) ≫ mpStr ℤ m n) e := hmp.of_isClosedImmersion (j ≫ i) hc hZd
      have hZ : GlobalTheory.IsArithVar (j ≫ i ≫ mpStr ℤ m n) e := by
        rw [← Category.assoc]
        exact hZ₀
      rcases Nat.eq_zero_or_pos e with rfl | he
      · have hcv := curve_eq' h₃ h₄ h₅ h₆ h₇ hPt hC hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hcv
        rw [H.point Z j hc hZd r₀ hr₀, hcv, HermLB.curveDeg, e₁]
        refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => (e₃ σ (mem_offSupp.2 ?_)).symm)
        rw [hZ.under_eq_genericPoint]
        exact CartierDiv.genericPoint_notMem_supp _
      · have hrc := rec_eq' h₅ h₆ h₇ hR II hII N A hN hA Z (j ≫ i) (Category.assoc _ _ _) e hZ
          (by simpa only [hcomp] using hP) r hr
        simp only [hcomp] at hrc
        rw [(H.recursion_one j hc he hZd hr₀).2, hrc, e₂, e₁]
        refine congrArg (· - _) (finsum_congr fun z' => ?_)
        by_cases hz : (((N.restr i).restr j).div hr₀).mult z' = 0
        · simp [hz]
        have hdz := h₄ Z _ e hZ z' (CartierDiv.coheight_eq_one_of_mult_ne_zero hz)
        rw [ih e (Nat.lt_succ_self e) (j z') ((dim_closure_image j z').trans hdz)]
  · obtain ⟨hpr, hz⟩ := hp₅ hW
    have key : ∀ p : ℕ, p.Prime → ((p : ℕ) : Γ(Z, ⊤)) = 0 → h (j (genericPoint Z)) =
        (geoNum d (ptIdeal (i (j (genericPoint Z)))) (fun _ => A.a) : ℝ) * Real.log p := by
      intro p hp h0
      haveI : Fact p.Prime := ⟨hp⟩
      haveI : CharP Γ(Z, ⊤) p := charP_of_cast hp h0
      letI : Algebra (ZMod p) Γ(Z, ⊤) := ZMod.algebra _ p
      have e₁ := H.vertical Z j (ZMod p) d hZd
      have e₂ : topSelfIntersection (ZMod p) ((N.restr i).B.pull j) d = _ := hV m n N A hN X i Z j p d hZd
      rw [e₁, e₂, Nat.card_zmod]
    rw [key _ hpr hz, cycVal, if_neg hW]

theorem heightEq_holds : PtDict → CodimOne → ExistsRat → CycleOfRat → ArchIntEq → VertEq → PtLen → CurveInt →
    RatRStatement → ∀ II : IntersectionSystem, IsFullIntersectionSystem II → HeightEq II :=
  fun h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII => heightEq_of h₃ h₄ h₅ h₆ h₇ hV hPt hC hR II hII

end GlobalTheory.CompanionTheory.MixZ
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HullGeneration
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

theorem typeB_of_mem_span {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {K : Subgroup (GL (Fin N) (Af E))} {W : Submodule ℂ (Kinf E N → ℂ)} {S : Set (Sm E N)}
    (hS : ∀ φ ∈ S, TypeB K W φ) {φ : Sm E N} (hφ : φ ∈ Submodule.span ℂ S) : TypeB K W φ := by
  induction hφ using Submodule.span_induction with
  | mem x hx => exact hS x hx
  | zero => exact ⟨fun _ _ _ => rfl, fun _ => W.zero_mem⟩
  | add x y _ _ hx hy =>
    refine ⟨fun u hu g => ?_, fun g => W.add_mem (hx.2 g) (hy.2 g)⟩
    show x.1 (g * finGL E N u) + y.1 (g * finGL E N u) = x.1 g + y.1 g
    rw [hx.1 u hu g, hy.1 u hu g]
  | smul c x _ hx =>
    refine ⟨fun u hu g => ?_, fun g => W.smul_mem c (hx.2 g)⟩
    show c • x.1 (g * finGL E N u) = c • x.1 g
    rw [hx.1 u hu g]

theorem hullGen : HullGen := by
  intro E _ _ _ N K W S hS hfd
  have hst : _root_.GlobalTheory.CuspRep.IsStable (hull S) := fun o φ hφ =>
    Submodule.mem_sInf.2 fun U hU => hU.2 o φ (Submodule.mem_sInf.1 hφ U hU)
  refine ⟨hst, ?_⟩
  have hsub : S ⊆ hull S := fun φ hφ => Submodule.mem_sInf.2 fun U hU => hU.1 hφ
  obtain ⟨t, ht⟩ := (Submodule.fg_iff_finiteDimensional _).2 hfd
  have htS : ∀ φ ∈ t, φ ∈ Submodule.span ℂ S := fun φ hφ => ht ▸ Submodule.subset_span hφ
  refine ⟨t, fun φ hφ => typeB_of_mem_span hS (htS φ hφ), fun φ hφ => ?_, fun U' hU' htU => ?_⟩
  · exact (Submodule.span_le.2 hsub) (htS φ hφ)
  · refine sInf_le ⟨?_, hU'⟩
    have h : Submodule.span ℂ S ≤ U' := ht ▸ Submodule.span_le.2 htU
    exact Submodule.subset_span.trans h

end GlobalTheory.CompanionTheory.EGlue

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HyperbolicFramesUnitaryStable
section
noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory _root_.Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf
open GlobalTheory.CompanionTheory.SW.ThetaStage

theorem linearIndependent_mulVec_GL {E : Type} [Field E] {M n : ℕ} (A : GL (Fin M) E)
    {X : Fin n → Fin M → E} (hX : LinearIndependent E X) :
    LinearIndependent E (fun a => (A : Matrix (Fin M) (Fin M) E) *ᵥ X a) := by
  have hinj : Function.Injective (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) := by
    intro x y hxy
    have h : ∀ v : Fin M → E, ((A⁻¹ : GL (Fin M) E) : Matrix (Fin M) (Fin M) E) *ᵥ
        ((A : Matrix (Fin M) (Fin M) E) *ᵥ v) = v := by
      intro v
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hxy' : (A : Matrix (Fin M) (Fin M) E) *ᵥ x = (A : Matrix (Fin M) (Fin M) E) *ᵥ y := hxy
    rw [← h x, ← h y, hxy']
  exact hX.map' (Matrix.mulVecLin (A : Matrix (Fin M) (Fin M) E)) (LinearMap.ker_eq_bot.2 hinj)

theorem gact_mem_framesE {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M n : ℕ}
    {J : Matrix (Fin M) (Fin M) E} (g : UJ (σ : E →+* E) J) {T : Matrix (Fin n) (Fin n) E}
    {q : Fin n → Fin M → E} (hq : q ∈ framesE σ J T) : gact σ g q ∈ framesE σ J T := by
  have h1 : LinearIndependent E (gact σ g q) := linearIndependent_mulVec_GL (g : GL (Fin M) E) hq.1
  have h2 : gramE σ J (gact σ g q) = T := by
    rw [gramE_gact]
    exact hq.2
  exact ⟨h1, h2⟩

theorem hypOne_basic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → IsHermND σ (hypOne J) ∧ e0 E M ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) ∧ ∀ (g : UJ (σ : E →+* E) (hypOne J)) (q : Fin 1 → Fin (M + 2) → E), q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) → gact σ g q ∈ framesE σ (hypOne J) (0 : Matrix (Fin 1) (Fin 1) E) := by
  intro F E _ _ _ _ _ σ _ M J hJ
  exact ⟨isHermND_hypOne σ hJ, e0_mem_framesE σ J, fun g q hq => gact_mem_framesE σ g hq⟩

end GlobalTheory.CompanionTheory.WeilSiegel.HypStep.Unf.Basic
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ImportsTer
section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTLink

theorem link : ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime]
    (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
    ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω (Dec (F := E) A) O),
      GlobalTheory.Pst.Induces Bw →
    ∀ (art : Ideles E →* Gab E Ω), IsGlobalArtin art →
    ∀ (χ : ↥(GK Bw.Kw) →* (↥Bw.Kw.1)ˣ), IsLTChar Bw.Kw χ →
    ∀ (φ : w.adicCompletion E →+* Om l), Continuous φ →
      (∀ y : E, φ (algebraMap E (w.adicCompletion E) y) = Bw.j (algebraMap E Ω y)) →
    ∀ (x : (w.adicCompletion E)ˣ) (σ : ↥(Dec (F := E) A)), IsUnitAt w x → (σ : G E Ω) ∈ Ine (F := E) A →
      art (localIdele E w x) = toAb E Ω σ →
      (((χ (Bw.e σ) : (↥Bw.Kw.1)ˣ) : ↥Bw.Kw.1) : Om l) = φ (x : w.adicCompletion E) := by
  intro E Ω _ _ _ _ _ l _ w A hA O _ _ _ Bw hI art hart χ hχ φ hφ hφj x σ hx hσ hxσ
  letI algF : Algebra (w.adicCompletion E) (Om l) := φ.toAlgebra
  have hmap : ∀ y, algebraMap (w.adicCompletion E) (Om l) y = φ y := fun _ => rfl
  have hr : Set.range (algebraMap (w.adicCompletion E) (Om l)) = (Bw.Kw.1 : Set (Om l)) :=
    _root_.GlobalTheory.CompanionTheory.LTHodge.CompletionRange.range_eq_Kw Bw w φ hφ hφj
  haveI hsep : IsSepClosure (w.adicCompletion E) (Om l) := _root_.GlobalTheory.CompanionTheory.LTHodge.isSepClosure_Om_of_range Bw.Kw hr
  haveI hext : ValuativeExtension (w.adicCompletion E) (Om l) := ⟨fun {a b} => by
    rw [GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le]
    exact (_root_.GlobalTheory.CompanionTheory.LocalNorm.vle_iff_norm_le φ hφ a b).symm⟩
  haveI hclosed : IsSepClosed (Om l) := IsSepClosure.sep_closed (w.adicCompletion E)
  haveI halg : Algebra.IsAlgebraic (w.adicCompletion E) (Om l) := hsep.separable.isAlgebraic
  obtain ⟨π, hπ, H⟩ := GlobalTheory.T.exists_uniformizer_galois_action hχ hr
  let g' := Bw.e σ
  have hfix : ∀ y, (g' : GQ l) (algebraMap (w.adicCompletion E) (Om l) y) = algebraMap (w.adicCompletion E) (Om l) y := by
    intro y
    have hy : algebraMap (w.adicCompletion E) (Om l) y ∈ Bw.Kw.1 := by
      have : algebraMap (w.adicCompletion E) (Om l) y ∈ (Bw.Kw.1 : Set (Om l)) := hr ▸ ⟨y, rfl⟩
      exact this
    exact g'.2 ⟨_, hy⟩
  let g : Om l ≃ₐ[w.adicCompletion E] Om l := { (g' : GQ l).toRingEquiv with commutes' := hfix }
  have hg : ∀ y, g y = (g' : GQ l) y := fun _ => rfl
  obtain ⟨u, hu, hact⟩ := H g g' hg
  have hdeg : unramifiedDegree (w.adicCompletion E) (Om l) g = 1 := GlobalTheory.T.local_bridge_lubin_tate_field Bw hI σ hσ g hg
  have hloc := GlobalTheory.T.lubin_tate_unramified_degree_one hπ (isLubinTateSeries_ltPoly π) u g hdeg hact
  have hres := fun (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L] =>
    _root_.GlobalTheory.CompanionTheory.LTLink.local_restriction_abelianization_artin w Bw.j (fun y => (hφj y).symm) (unitsIncl _ u⁻¹) (σ : G E Ω) g
      (fun z => by rw [hg]; exact Bw.e_comm σ z) hloc L
  have h1 : art (localIdele E w (unitsIncl _ u)) = toAb E Ω σ := by
    rw [_root_.GlobalTheory.CompanionTheory.ArtinMapUniq.eq_inv_arithmetic_artin_map art hart]
    have hb : ∀ a b : Gab E Ω, (∀ (L : IntermediateField E Ω) [FiniteDimensional E L] [IsAbelianGalois E L],
        PositivityTheory.FamInh.res L a = PositivityTheory.FamInh.res L b) → a = b := by
      intro a b h
      have := PositivityTheory.FamInh.mem_of_forall_res (H := ⊥) (g := a * b⁻¹) (by simpa using isClosed_singleton)
        fun L _ _ _ => by rw [map_mul, map_inv, h L, mul_inv_cancel]
      exact mul_inv_eq_one.1 (Subgroup.mem_bot.1 this)
    refine hb _ _ fun L _ _ => ?_
    rw [hres L, MonoidHom.inv_apply, map_inv, map_inv]
    simp
  have h2 : unitsIncl _ u = x :=
    GlobalTheory.ArtinLocalInj.artin_localIdele_injective GlobalTheory.Published.chevalleyUnits' E Ω art hart w (h1.trans hxσ.symm)
  rw [← hu, ← h2]
  rfl

end GlobalTheory.CompanionTheory.LTLink
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InfinitesimalCharacterConjugateStatement
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.infinitesimal_character_conjugate : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ), IsHerm π B → ∀ (τ : E →+* ℂ) (m m' : Multiset ℂ), π.HasInfChar τ m → π.HasInfChar (NumberField.ComplexEmbedding.conjugate τ) m' → m' = m.map fun z => -(starRingEnd ℂ) z := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | exact GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq | (intros; apply GlobalTheory.CompanionTheory.Clozel.hasInfChar_conj_eq <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientIff
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OnePart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hasSat_iff {π : CuspSub E n} {w : HeightOneSpectrum (𝓞 E)} {τ : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (hτ : π.IsLocComp w τ) (B : Multiset ℂˣ) : (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w τ.ρ B := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  obtain ⟨α, hαB, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π h hτ
  rw [← hαB]
  exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n _ _ _ hα

end GlobalTheory.CompanionTheory.OnePart

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsUnderOfSameOrbit
section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.ProjSpace GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.ArInt GlobalTheory.Points GlobalTheory.ChartGlue
open GroundTheory.Arith.SchemeCoh GroundTheory.Arith.SchemeCoh.ProjSpace
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.MPDict GlobalTheory.CompanionTheory.MixZ
open ReciprocityTheory.ChartRestriction.G.Geo (mcPts IsMultiHomog SameOrbit)

namespace GlobalTheory.CompanionTheory.MixZ.Orbit

theorem isUnder_of_sameOrbit : ∀ (m : ℕ) (n : Fin (m + 1) → ℕ) (w : GlobalTheory.CxPts (mpStr ℤ m n) σ₀) (z z' : (Σ k, Bk n k) → ℂ),
    IsUnder w z → SameOrbit z' z → IsUnder w z' := by
  rintro m n w z z' h ⟨c, hc, rfl⟩ k i
  refine ⟨(h k i).1.trans ?_, fun j hy => ((h k i).2 j hy).trans ?_⟩
  · show z ⟨k, i⟩ ≠ 0 ↔ c k * z ⟨k, i⟩ ≠ 0
    simp [hc k]
  · exact (mul_div_mul_left _ _ (hc k)).symm

end GlobalTheory.CompanionTheory.MixZ.Orbit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicityPosStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_pos : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {h N : ℕ} (x : Fin h → IrrGL (k := k)) (hd : ∑ a, (x a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (τ : Representation ℂ (GL (Fin N) k) V), IsSmooth τ → ∀ f : τ.IntertwiningMap (prodIrr x hd), (∃ v, f v ≠ 0) → 1 ≤ jm x hd τ := by
  first | exact @GlobalTheory.CompanionTheory.FrobJm.one_le_jm | exact GlobalTheory.CompanionTheory.FrobJm.one_le_jm | (intros; apply GlobalTheory.CompanionTheory.FrobJm.one_le_jm <;> assumption)
end

