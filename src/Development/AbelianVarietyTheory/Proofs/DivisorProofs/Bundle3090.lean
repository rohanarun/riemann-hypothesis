module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3084
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1210
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1159
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1152
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1867
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1190
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2768
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.BaseChangeMapRingAct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2770
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2111
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2301
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsBlockMetricDiagForm
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.LawsProved
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2875
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2895
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3085
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2283
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0691
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2848
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1945
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0657
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2447
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrystallinePull2SumCup
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2069
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLcCutPointOfNotLcOther
section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

namespace GlobalTheory.PairStep

theorem exists_lcCut_of_not_lcAt : GlobalTheory.Published.Principalisation → GlobalTheory.Published.NadelVanishingPair → GlobalTheory.Published.NefNumerics → ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (p : X ⟶ Sp ℂ) (n : ℕ), IsProjOver p → topologicalKrullDim X = n → letI := algebraΓOfHom p; ∀ (Δ : X → ℚ) (m : ℕ) (G : CartierDiv X) (N : LB X) (D : X → ℚ) (d h : ℚ) (x x' z : X) (j : ℕ), IsEffQDiv Δ → (∀ y, KltAt p n Δ y) → 0 < m → IsLogCanonicalMultiple p n Δ m G → IsAmpleLB N → QNum p N d D → 0 ≤ d → IsClosed ({x} : Set X) → LcAt p n (Δ + D) x → ¬ LcAt p n (Δ + D) x' → z ⤳ x → IsNkltCentre p n (Δ + D) z → topologicalKrullDim (closure ({z} : Set X)) = (j + 1 : ℕ) → 0 < h → ((j + 1 : ℕ) : ℚ) ^ (j + 1) < h ^ (j + 1) * (interNumRed ℂ (Closeds.closure ({z} : Set X)) fun _ : Fin (j + 1) => N : ℤ) → ∃ (D' : X → ℚ) (d' : ℚ), 0 ≤ d' ∧ d' ≤ d + h ∧ QNum p N d' D' ∧ LcCut p n (Δ + D') x j ∧ ¬ KltAt p n (Δ + D') x' := by
  intro hPr hNad hNef X _ _ _ p n hp hn Δ m G N D d h x x' z j hΔ hklt hm hG hN hQ hd hx hlc hnlc
    hzx hz hzd hh hdeg
  have hDq : IsQCart D := QNum.isQCart hQ

  obtain ⟨B, δ₀, hδ₀, hδ₀1, hBq, hoff, hnk, hfar⟩ :=
    GlobalTheory.T.exists_divisor_nonKlt_at_points_not_containing_centre hPr hNad hNef X p n hp hn Δ m G N D {x} z (j + 1) h hΔ hklt hm hG hN hDq
      (by simp [hx, hzx]) (by omega) hzd (Or.inr hz) hh (by simpa using hdeg)

  obtain ⟨δ₁, hδ₁, hx'⟩ := _root_.GlobalTheory.PairStep.not_kltAt_sub_of_not_lcAt X p n hp hn Δ D x' hDq (hklt x') hnlc
  obtain ⟨δ, hδ, hδ1, hδa, hδb⟩ : ∃ δ : ℚ, 0 < δ ∧ δ ≤ 1 ∧ δ ≤ δ₀ ∧ δ ≤ δ₁ :=
    ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, (min_le_left _ _).trans hδ₀1, min_le_left _ _, min_le_right _ _⟩
  have hBc : IsQCart B := QNum.isQCart hBq
  have hDδ : IsQCart ((1 - δ) • D) := (_root_.GlobalTheory.QCartCone.isQCart_cone X D D (1 - δ) hDq hDq (by linarith)).2.1

  have hkx : KltAt p n (Δ + (1 - δ) • D) x := _root_.GlobalTheory.PairStep.kltAt_add_smul_of_lcAt X p n hp hn Δ D δ x hDq (hklt x) hlc hδ hδ1
  have hnkx : ¬ KltAt p n (Δ + (1 - δ) • D + B) x := hnk δ hδ.le hδa x (Finset.mem_singleton_self x)

  obtain ⟨c, hc, hc1, hlcx, hnklx⟩ :=
    _root_.GlobalTheory.PairStep.exists_threshold_lcAt_not_kltAt hPr X p n hp hn Δ m G ((1 - δ) • D) B x hm hG hDδ hBc hkx hnkx
  have hcut : LcCut p n (Δ + (1 - δ) • D + c • B) x j :=
    _root_.GlobalTheory.PairStep.logCanonicalCut_of_step X p n hp hn Δ D B δ c x z j (hklt x) hDq hBc hlc hδ hδ1 hc1 hoff hfar hzd hlcx hnklx
  refine ⟨(1 - δ) • D + c • B, (1 - δ) * d + c * h, ?_, ?_, ?_, ?_, ?_⟩
  · have : 0 ≤ 1 - δ := by linarith
    positivity
  · nlinarith [mul_nonneg hδ.le hd, mul_le_mul_of_nonneg_right hc1 hh.le]
  · exact qNum_add X p hp N _ _ _ _ (_root_.GlobalTheory.PairStep.qNum_smul X p hp N d (1 - δ) D (by linarith) hQ)
      (_root_.GlobalTheory.PairStep.qNum_smul X p hp N h c B hc.le hBq)
  · rw [← add_assoc]
    exact hcut
  ·
    intro hk
    rw [← add_assoc] at hk
    have h0 := (_root_.GlobalTheory.PairStep.kltAt_lcAt_of_le_coeff X p n hp hn (Δ + (1 - δ) • D) B 0 c x' hBc hc.le).1 hk
    rw [zero_smul, add_zero] at h0
    exact hx' δ hδ.le hδb h0

end GlobalTheory.PairStep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPDivGroupTower
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB mulN)
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
open GlobalTheory.DeRham (spOver)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AbelianTower

open TensorProduct
open scoped CategoryTheory.Obj

theorem exists_isUnivTorsion {O : Type} [CommRing O] {A : Over (Sp O)} [GrpObj A] (hA : IsAbelianScheme A) {g : ℕ}
    (hg : SmoothOfRelativeDimension g A.hom) {N : ℕ} (hN : N ≠ 0) :
    ∃ (R : Type) (_ : CommRing R) (_ : Algebra O R) (y : SpAlg O R ⟶ A), Module.Finite O R ∧
      Module.Projective O R ∧ AbelianPDiv.IsUnivTorsion N y ∧
      ∀ q : PrimeSpectrum O, Module.rankAtStalk R q = N ^ (2 * g) := by
  obtain ⟨R, _, _, y, h1, h2, h⟩ := AbelianPDiv.exists_isPullback (N := N) hA (Nat.one_le_iff_ne_zero.2 hN)
  refine ⟨R, inferInstance, inferInstance, y, h1, h2, AbelianPDiv.isUnivTorsion_of_isPullback y h, fun q => ?_⟩
  let K := q.asIdeal.ResidueField
  obtain ⟨y', h'⟩ := AbelianPDiv.exists_isPullback_baseChange y h K
  let B : AV.AbVar K :=
    { X := (Over.pullback (spMap (algebraMap O K))).obj A
      ab := ReciprocityTheory.ChartRestriction.G.Out.TLinPf.isAb_pullback _ A hA
      dim := g
      smooth := (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback A.hom (spMap (algebraMap O K))) hg }
  have hr := AVTower.finrank_torsion B hN (S := K ⊗[O] R) y' h'
  have hq : PrimeSpectrum.comap (algebraMap O K) ⊥ = q :=
    PrimeSpectrum.ext ((RingHom.ker_eq_comap_bot _).symm.trans (Ideal.ker_algebraMap_residueField _))
  rw [← hq, ← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free, hr]
  rfl

theorem exists_pDivGroup (p : ℕ) [hp : Fact p.Prime] (O : Type) [CommRing O] (A : Over (Sp O)) [GrpObj A]
    (hA : IsAbelianScheme A) (g : ℕ) (hg : SmoothOfRelativeDimension g A.hom) :
    ∃ (G : PDivGroup p O) (_ : G.TorsionTower A), G.height = 2 * g := by
  have := hA.comm
  choose R _ _ y h1 h2 h hr using fun n : ℕ => exists_isUnivTorsion (N := p ^ n) hA hg
    (pow_ne_zero _ hp.out.ne_zero)
  choose r r1 r2 r3 using fun n : ℕ => (h n).exists_res (h (n + 1))
    (by rw [pow_succ, pow_mul, (h n).1, one_pow])
  let G : PDivGroup p O :=
    { height := 2 * g
      A := R
      hopf := fun n => (h n).hopfAlgebra
      cocomm := fun n => (h n).isCocomm
      finite := h1
      projective := h2
      rank_eq := fun n q => (hr n q).trans (pow_mul _ _ _).symm
      res := r
      res_surjective := r1
      ker_res := r2 }
  exact ⟨G, {
    y := y
    mul := fun n B _ _ => (h n).mul_y
    inj := fun n B _ _ _ _ => (h n).inj
    surj := fun n B _ _ z hz => ((h n).2 B z hz).exists
    res := r3 }, rfl⟩

theorem exists_pDivGroup_tower : ∀ (p : ℕ) [Fact p.Prime] (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∃ (G : PDivGroup p R) (_ : G.TorsionTower A), G.height = 2 * g :=
  fun p _ R _ _ A _ g hA hg => exists_pDivGroup p R A hA g hg

end GlobalTheory.AbelianTower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRepAdjointActionLevelSiegelPullback
section
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

theorem exists_finite_rep_rosati_level : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) [IsLocallyNoetherian S] (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∃ (E : Scheme.{0}) (πE : E ⟶ S) (AE : Over E) (_ : GrpObj AE) (_ : IsCommMonObj AE) (φE : AE.left ⟶ c.A.left) (φ₂E : (G2 AE).left ⟶ (G2 c.A).left) (actE : OActN D.O AE) (ηE : D.La → (𝟙_ (Over E) ⟶ AE)), IsLocallyNoetherian E ∧ IsFinite πE ∧ IsGrpPullback AE c.A πE φE ∧ IsSquare φE φ₂E ∧ RosatiFor D actE (c.P.pull φ₂E) ∧ EtaOK D N actE ηE ∧ ∀ (T : Scheme.{0}) (g : T ⟶ S) (AT : Over T) [GrpObj AT] (φ : AT.left ⟶ c.A.left) (φ₂ : (G2 AT).left ⟶ (G2 c.A).left) (act : OActN D.O AT) (eta : D.La → (𝟙_ (Over T) ⟶ AT)), IsGrpPullback AT c.A g φ → IsSquare φ φ₂ → RosatiFor D act (c.P.pull φ₂) → EtaOK D N act eta → ∃! z : T ⟶ E, z ≫ πE = g ∧ ∃ ψ : AT.left ⟶ AE.left, IsGrpPullback AT AE z ψ ∧ ψ ≫ φE = φ ∧ (∀ a : D.O, (act.act a).left ≫ ψ = ψ ≫ (actE.act a).left) ∧ ∀ y, (eta y).left ≫ ψ = z ≫ (ηE y).left := by
  intro p _ D R _ b N hNp h M B _ ζ S _ s₁ t c e he hc
  obtain ⟨H, πH, AH, _, _, φH, φ₂H, actH, hHf, hHab, pbH, sqH, rosH, univH⟩ := GlobalTheory.T.exists_finite_rep_rosati_orderActions_siegel p D h M B ζ S s₁ c hc.1
  have hNH : IsUnit ((N : ℕ) : Γ(H, ⊤)) := by
    have h0 : IsUnit ((N : ℕ) : Γ(Sp R, ⊤)) := by
      have := (b.unit N hNp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
      simpa using this
    have := h0.map (πH ≫ t).appTop.hom
    simpa using this
  obtain ⟨E, πE, AE, _, _, φE, actE, ηE, hEf, pbE, actEc, etaE, univE⟩ := GlobalTheory.T.exists_finite_representing_linearLevels_abelianScheme p D N H AH hHab hNH actH
  let x₁ : Over.mk ((G2 AE).hom ≫ πE) ⟶ AH :=
    Over.homMk ((fst AE AE).left ≫ φE) (by rw [Category.assoc, pbE.1.w, ← Category.assoc, Over.w]; rfl)
  let x₂ : Over.mk ((G2 AE).hom ≫ πE) ⟶ AH :=
    Over.homMk ((snd AE AE).left ≫ φE) (by rw [Category.assoc, pbE.1.w, ← Category.assoc, Over.w]; rfl)
  let φ₂ : (G2 AE).left ⟶ (G2 AH).left := (lift x₁ x₂).left
  have sq : IsSquare φE φ₂ := by
    constructor
    · show (lift x₁ x₂).left ≫ (fst AH AH).left = _
      rw [← Over.comp_left, lift_fst]; rfl
    · show (lift x₁ x₂).left ≫ (snd AH AH).left = _
      rw [← Over.comp_left, lift_snd]; rfl
  haveI : IsLocallyNoetherian H := LocallyOfFiniteType.isLocallyNoetherian πH
  haveI : IsLocallyNoetherian E := LocallyOfFiniteType.isLocallyNoetherian πE
  refine ⟨E, πE ≫ πH, AE, inferInstance, inferInstance, φE ≫ φH, φ₂ ≫ φ₂H, actE, ηE, inferInstance,
    inferInstance, pbE.comp pbH, ?_, GlobalTheory.T.rosatiCondition_of_grpPullback_square p D S H E c.A c.P c.isLB AH AE πE φE φ₂ φ₂H actH actE pbE sq actEc rosH,
    etaE, ?_⟩
  · constructor
    · rw [Category.assoc, sqH.1, ← Category.assoc, sq.1, Category.assoc]
    · rw [Category.assoc, sqH.2, ← Category.assoc, sq.2, Category.assoc]
  intro T g AT _ φ φ₂' act eta pbT sqT rosT etaT
  obtain ⟨z₁, ⟨hz₁, ψ₁, pb₁, hψ₁, act₁⟩, uniq₁⟩ := univH T g AT φ φ₂' act pbT sqT rosT
  obtain ⟨z, ⟨hz, ψ, pb, hψ, heta⟩, uniq⟩ := univE T z₁ AT ψ₁ act eta pb₁ act₁ etaT
  refine ⟨z, ⟨by rw [← Category.assoc, hz, hz₁], ψ, pb, by rw [← Category.assoc, hψ, hψ₁], fun a => ?_, heta⟩, ?_⟩
  · apply pbE.1.hom_ext
    · rw [Category.assoc, hψ, act₁, Category.assoc, actEc, ← Category.assoc, hψ]
    · rw [Category.assoc, pb.1.w, Category.assoc, Over.w (actE.act a), pb.1.w, ← Category.assoc, Over.w (act.act a)]
  · rintro z' ⟨hz', ψ', pb', hψ', act', eta'⟩
    have e₁ : z' ≫ πE = z₁ := uniq₁ (z' ≫ πE) ⟨by rw [Category.assoc]; exact hz', ψ' ≫ φE, pb'.comp pbE,
      by rw [Category.assoc]; exact hψ', fun a => by
        rw [← Category.assoc, act' a, Category.assoc, actEc, Category.assoc]⟩
    have e₂ : ψ' ≫ φE = ψ₁ := by
      apply pbH.1.hom_ext
      · rw [Category.assoc, hψ', hψ₁]
      · rw [Category.assoc, pbE.1.w, ← Category.assoc, pb'.1.w, Category.assoc, e₁, pb₁.1.w]
    exact uniq z' ⟨e₁, ψ', pb', e₂, eta'⟩

end GlobalTheory.UPel.HT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymmetricKodairaSpencerAbelianLocus
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSAbLocusSymm

theorem tanBasis_of_basis' {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R]
    (t : SAB H (Sp R)) {n : ℕ} (b : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) {T : Type} [CommRing T]
    (φ : R →+* T) :
    (∀ i, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) (spMap (dualMap φ) ≫ (tv (b i)).left)) ∧
      ∀ w, IsTanAtG t (spMap φ ≫ 𝟙 (Sp R)) w →
        ∃! a : Fin n → T, IsCombAtG t (spMap φ ≫ 𝟙 (Sp R)) (fun i => spMap (dualMap φ) ≫ (tv (b i)).left) a w := by
  refine GlobalTheory.LocM.FrameBase.tanBasis_baseChange t φ (𝟙 (Sp R)) n _ (fun i => GlobalTheory.LieMet.isTan_tv (b i)) ?_
  intro w hw
  refine ⟨b.repr (GlobalTheory.LieMet.tanOf hw), ?_, fun a ha => ?_⟩
  · show IsCombAtG t _ _ _ (tv (GlobalTheory.LieMet.tanOf hw)).left
    rw [GlobalTheory.LieMet.isComb_iff]
    exact (b.sum_repr _).symm
  · have h := (GlobalTheory.LieMet.isComb_iff b a (GlobalTheory.LieMet.tanOf hw)).1 ha
    rw [h]
    ext i
    simp [Finsupp.single_apply]

theorem exists_symm_isKS_abLocus : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] [Algebra ℚ R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (m : ℕ) (tt : Fin m → R) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre tt gam → (∀ i, tt i ≠ 0) → (∀ p : Sp R, p ∈ abLocus t.G ↔ ∏ i, tt i ∉ p.asIdeal) → ∀ (n : ℕ) (v' : Module.Basis (Fin n) R (TanM (𝟙 (Sp R)) t.G)) (DV : Derivation ℤ Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1)), ∃ Θ₁ : Matrix (Fin n) (Fin n) Γ(Sp R, ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))).1), Θ₁ᵀ = Θ₁ ∧ IsKS t ((Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) ((Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens)) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))) (fun a => spMap (dualMap (((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)) ≫ (tv (v' a)).left) ⇑DV Θ₁ := by
  intro E _ _ _ H R _ _ _ _ _ _ t P m tt gam hmon htt hab n v' DV
  obtain ⟨Θ₁, hKS⟩ := GlobalTheory.T.exists_kodairaSpencer_abelianLocus_chartRing E H R t P m tt gam hmon htt hab n v' 0 DV
  refine ⟨Θ₁, ?_, hKS⟩
  let U : (Sp R).affineOpens := (Sp R).affineBasicOpen (U := (⟨⊤, isAffineOpen_top _⟩ : (Sp R).affineOpens))
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i))
  let ρ : R →+* Γ(Sp R, U.1) := ((Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom
  have hc : spMap ρ ≫ 𝟙 (Sp R) = chart U := by
    rw [Category.comp_id]
    show Spec.map _ = U.2.fromSpec
    rw [← (isAffineOpen_top (Sp R)).map_fromSpec U.2 (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op, IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec]
    rw [show CommRingCat.ofHom ρ = (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE ((Sp R).basicOpen_le (U := ⊤)
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (∏ i, tt i)))).op from rfl]
    erw [Spec.map_comp]
    rfl
  obtain ⟨hv, hb⟩ := tanBasis_of_basis' t v' ρ
  rw [hc] at hv hb
  have h2 : (U.1 : (Sp R).Opens) = PrimeSpectrum.basicOpen (∏ i, tt i) :=
    basicOpen_eq_of_affine (R := CommRingCat.of R) (∏ i, tt i)
  have h4 : ∀ q : Sp R, q ∈ ((U.1 : (Sp R).Opens) : Set (Sp R)) → ∏ i, tt i ∉ q.asIdeal := by
    intro q hq
    rw [h2] at hq
    exact hq
  have hx : ∀ s, ∏ i, tt i ∉ ((chart U) s).asIdeal := fun s =>
    h4 _ (by rw [← U.2.range_fromSpec]; exact ⟨s, rfl⟩)
  have hne : ∏ i, tt i ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => htt i
  haveI : Nonempty (U.1 : (Sp R).Opens) := by
    refine ⟨⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R), ?_⟩⟩
    show _ ∈ ((U.1 : (Sp R).Opens) : Set (Sp R))
    rw [h2]
    show ∏ i, tt i ∉ (⊥ : Ideal R)
    simpa using hne
  haveI : IsDomain Γ(Sp R, U.1) := inferInstance
  let K := FractionRing Γ(Sp R, U.1)
  let x₀ : Γ(Sp R, U.1) →+* K := algebraMap _ _
  letI : Algebra ℚ K := ((x₀.comp ρ).comp (algebraMap ℚ R)).toAlgebra
  haveI : CharZero K := algebraRat.charZero K
  obtain ⟨PP', cub, sym, adj, prim, mm, -⟩ := sabPull proved_CubePullSt (spMap x₀ ≫ chart U) t
  have hx' : ∀ s, ∏ i, tt i ∉ ((spMap x₀ ≫ chart U) s).asIdeal := fun s => hx ((spMap x₀) s)
  obtain ⟨hP, hA, hK⟩ := GlobalTheory.AbLocusPol.isProper_relAmple_kTriv_of_abLocus E H R t P m tt htt hab _
    (spMap x₀ ≫ chart U) _ hx' ⟨mm⟩
  obtain ⟨P₀, e, he⟩ := GlobalTheory.PolDvr.exists_polAV _ hP hA hK
  obtain ⟨w, g, -⟩ := mm.lin
  obtain ⟨h1, h2'⟩ := he t.G (spMap x₀ ≫ chart U) mm.φ t.PP.L mm.cart ⟨w, g⟩
  have hsym := GlobalTheory.FibSym.map_transpose_eq E H (Sp R) t _ U n _ hv hb K x₀ P₀ _ h1 h2' le_rfl _ Θ₁ hKS
  ext i j
  have hij := congrFun (congrFun hsym i) j
  simp only [Matrix.transpose_apply, Matrix.map_apply] at hij
  exact IsFractionRing.injective Γ(Sp R, U.1) K hij

end GlobalTheory.KSAbLocusSymm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorExistsLiftOrderActionHodgeSummand
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTDeform

theorem connectedSpace_sp_of_local (C : Type) [CommRing C] [IsLocalRing C] : ConnectedSpace (Sp C) := by
  have : PreconnectedSpace (PrimeSpectrum C) := by
    refine ⟨isPreconnected_of_forall (IsLocalRing.closedPoint C) fun y _ ↦
      ⟨closure {y}, Set.subset_univ _, ?_, subset_closure rfl, isPreconnected_singleton.closure⟩⟩
    exact (IsLocalRing.specializes_closedPoint y).mem_closure
  have : ConnectedSpace (PrimeSpectrum C) := ⟨inferInstance⟩
  exact this

theorem exists_lift_oAct : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ) (C C₀ : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [CommRing C₀] (π : C →+* C₀), Function.Surjective π → ∀ (hsq : RingHom.ker π ^ 2 = 0) (tR : R →+* C) (o₀ : GlobalTheory.UPel.HT.Obj b N (spMap π ≫ spMap tR)), ∀ (E : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A)), (∃ M : Submodule C (Crys (divided₂ hsq) (spMap π) o₀.A), IsCompl E M) → (∀ y : HdR o₀.A, y ∈ Fil o₀.A ↔ ∃ d ∈ E, (GlobalTheory.Published.GrothendieckMessing.crysRedMor (divided₂ hsq) rfl o₀.A).Corr d y) → (∀ (c : D.O), ∀ d ∈ E, (haveI := o₀.act.hom (c); push (divided₂ hsq) (spMap π) (o₀.act.act (c)) (d)) ∈ E) → ∃ (A : Over (Sp C)) (_ : GrpObj A) (i : o₀.A.left ⟶ A.left) (h : IsGrpPullback o₀.A A (spMap π) i) (act : GlobalTheory.UPel.HT.OActN D.O A), IsAbelianScheme A ∧ liftFil (divided₂ hsq) h = E ∧ ∀ c, (o₀.act.act c).left ≫ i = i ≫ (act.act c).left := by
  intro p _ D R _ b N C C₀ _ _ _ _ π hπ hsq tR o₀ E hE hFil hstab
  have GD := GlobalTheory.Published.grothendieckDeformation_of_lifting _root_.GlobalTheory.abelianDeRham _root_.GlobalTheory.abelianScheme_hom_lifting_nilpotent_dividedPowers
  have hκ := isDPNilpotent_squareZero hsq
  obtain ⟨A₁, _, i₁, h₁, hA₁⟩ := _root_.GlobalTheory.UnobTop.abelianUnobstructed C (RingHom.ker π) hsq C₀ π hπ rfl o₀.A o₀.ab
  haveI := hA₁.smooth
  haveI := hA₁.geomConnected
  haveI := connectedSpace_sp_of_local C
  haveI : ConnectedSpace A₁.left := GeometricallyConnected.connectedSpace A₁.hom A₁.hom.isOpenMap
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected A₁.hom (Classical.arbitrary _)
  obtain ⟨A, _, i, h, hA, hgA, hE'⟩ :=
    GlobalTheory.RMDeform.exists_lift_abelian GD _root_.GlobalTheory.abelianDeRham (divided₂ hsq) hκ π hπ rfl h₁ hA₁ hg E hE hFil
  haveI : IsCommMonObj A := hA.comm
  have HL := (GD C _ (divided₂ hsq) hκ C₀ π hπ rfl).2.2
  have key : ∀ c : D.O, ∃! f : A ⟶ A, IsMonHom f ∧ i ≫ f.left = (o₀.act.act c).left ≫ i := fun c ↦ by
    haveI := o₀.act.hom c
    exact HL g o₀.A A i h hA hgA g o₀.A A i h hA hgA (o₀.act.act c) (fun d hd ↦ by
      rw [hE'] at hd ⊢; exact hstab c d hd)
  choose f hf huniq using key
  refine ⟨A, inferInstance, i, h, ⟨f, fun c ↦ (hf c).1, ?_, ?_, ?_⟩, hA, hE', fun c ↦ (hf c).2.symm⟩
  · refine (huniq 1 (𝟙 _) ⟨inferInstance, ?_⟩).symm
    rw [o₀.act.one]
    simp
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x * y) (f y ≫ f x) ⟨inferInstance, ?_⟩).symm
    rw [o₀.act.mul, Over.comp_left, Over.comp_left, ← Category.assoc, (hf y).2, Category.assoc, (hf x).2,
      Category.assoc]
  · intro x y
    haveI := (hf x).1
    haveI := (hf y).1
    refine (huniq (x + y) (f x * f y) ⟨GlobalTheory.OActLift.isMonHom_mul_of_comm _ _, ?_⟩).symm
    rw [o₀.act.add]
    let j : Over.mk (o₀.A.hom ≫ spMap π) ⟶ A := Over.homMk i h.1.w
    have e := h.2 o₀.A (o₀.act.act x) (o₀.act.act y) (j ≫ f x) (j ≫ f y) (hf x).2 (hf y).2
    rw [← MonObj.comp_mul] at e
    exact e

end GlobalTheory.HTDeform
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPairingSkewHodgeLagrangian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.UPel.HT.FormFacts
open GlobalTheory.AbDual

theorem formFacts : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → FiniteDimensional k (HdR o₀.A) ∧ 2 * Module.finrank k (Fil o₀.A) = Module.finrank k (HdR o₀.A) ∧ (∀ x y, φ x y = -φ y x) ∧ ∀ x ∈ Fil o₀.A, ∀ y ∈ Fil o₀.A, φ x y = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β _ φ hφ
  have H := GlobalTheory.abelianDeRham
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  obtain ⟨hfd, hdimH, hdimF⟩ := GlobalTheory.finrank_HdR_Fil_of_field H.1 H.2.1 k o₀.A g o₀.ab hg
  have hAB := AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab
  have gAB := smooth_prod hg hg
  have C := cupSquare_of_free H.1 hAB gAB
  refine ⟨hfd, by rw [hdimH, hdimF], GlobalTheory.SymmPoincare.skew_of_symm C o₀.isLB (LBIso.symm o₀.symm) hφ, ?_⟩
  obtain ⟨ψ, hψ, e⟩ := hφ.isPolForm
  obtain ⟨iso, -⟩ := H.2.2.2.2 k _ _ hAB gAB o₀.P o₀.isLB ψ hψ
  intro x hx y hy
  have a₁ : push (dp0 k) (𝟙 _) (fst o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) = x := by
    rw [push_push _ _ _ (lift_fst _ _), push_id]; rfl
  have a₂ : push (dp0 k) (𝟙 _) (snd o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) = 0 := by
    rw [push_push _ _ _ (lift_snd _ _), push_one]; rfl
  have b₁ : push (dp0 k) (𝟙 _) (fst o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) = 0 := by
    rw [push_push _ _ _ (lift_fst _ _), push_one]; rfl
  have b₂ : push (dp0 k) (𝟙 _) (snd o₀.A o₀.A) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) = y := by
    rw [push_push _ _ _ (lift_snd _ _), push_id]; rfl
  have key : φ x y = ψ (push (dp0 k) (𝟙 _) (inl o₀.A o₀.A) x) (push (dp0 k) (𝟙 _) (inr o₀.A o₀.A) y) := by
    rw [e, a₁, a₂, b₁, b₂]; simp
  rw [key]
  exact iso _ (push_mem_Fil _ hx) _ (push_mem_Fil _ hy)

end GlobalTheory.UPel.HT.FormFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackBundleDualHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

open GlobalTheory.AbDual GlobalTheory.CechPic

theorem pullPol_dual_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ' : B ⟶ o.A), IsAbelianScheme B → IsMonHom ψ' → ∃ (C : Over Y) (_ : GrpObj C) (Q : LB (B ⊗ C).left) (h : B ⟶ C), IsAbelianScheme C ∧ GlobalTheory.AbDual.IsDual B C Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (o.P.pull (ψ' ⊗ₘ ψ').left) (Q.pull (lift (fst B B) (snd B B ≫ h)).left) ∧ ∀ (T : Over Y) (x : T ⟶ B), PullPolTriv o ψ' x ↔ x ≫ h = 1 := by
  intro p _ D R _ b N Y s o B _ _ ψ' hB hψ
  obtain ⟨C, _, Q, h, hC, hQ, hQ', hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom Y B o.A ψ' o.P hB o.ab hψ o.isLB o.rig₁ o.rig₂
  refine ⟨C, inferInstance, Q, h, hC, hQ, hQ', hh, e, fun T x ↦ ?_⟩
  have eχ : ψ' ⊗ₘ ψ' = lift (fst B B ≫ ψ') (snd B B ≫ ψ') := by ext <;> simp
  rw [eχ] at e
  have hE : (ev o.P (fst B B ≫ ψ') (snd B B ≫ ψ')).IsLB := pull_isLB o.isLB _
  have hF : (ev Q (fst B B) (snd B B ≫ h)).IsLB := pull_isLB hQ.isLB _
  have c := congrArg (CechPic.pull (lift (fst B T) (snd B T ≫ x)).left) ((cls_eq_iff hE hF).2 e)
  rw [cls_ev o.isLB, cls_ev hQ.isLB, pull_evc, pull_evc, lift_fst_assoc, lift_snd_assoc, lift_fst,
    lift_snd_assoc] at c
  simp only [Category.assoc] at c
  have k : PullPolTriv o ψ' x ↔ evc o.isLB (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ') = 0 :=
    triv_ev_iff o.isLB _ _
  rw [k, c]
  constructor
  · intro z
    exact hQ.eq_one (x ≫ h) ((triv_ev_iff hQ.isLB _ _).2 z)
  · intro z
    rw [z, MonObj.comp_one]
    exact evc_one_right hQ.isLB hQ.zero _

end GlobalTheory.UPel.HT.ES
end

