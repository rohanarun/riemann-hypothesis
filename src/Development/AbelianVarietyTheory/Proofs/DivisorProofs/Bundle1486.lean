module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsVeryAmpleBySectionsOfInvertibleLinearChange
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1460
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.CoeNonzeroLocusCanonicalEqComplRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0718
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0012
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0012
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PFamily
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PStdOK
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0290
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ExistsPowPrincipalFractionalIdeal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1468
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.TheoremA
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsImageHeightUnique
public import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
public import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0005
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0414
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Spread
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1469
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1407
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1398
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1432
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1470
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MorphismToProjSpacePreimageNonzeroLocusLinearFor
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)

noncomputable section

namespace GlobalTheory.SpanVA

open TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi (LB)
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp PSpace resG)
open GlobalTheory.ProjSpace (toProj O1 coord)

theorem comb_f {R : Type} [CommRing R] {X : Scheme.{0}} {H : LB X} {n : ℕ} (g : X ⟶ Sp R) (c : Fin n → R)
    (t : Fin n → H.Sec) (k : H.ι) :
    (∑ j, GlobalTheory.AbLaw.cst g ⊤ (c j) • t j).f k = ∑ j, GlobalTheory.AbLaw.cst g (H.U k) (c j) * (t j).f k := by
  rw [GlobalTheory.LinChange.sum_f]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [GlobalTheory.LB.smul_f, GlobalTheory.LinChange.resG_cst]

theorem secPull_comb_f {R : Type} [CommRing R] {X Y : Scheme.{0}} {L : LB X} {n : ℕ} (p : X ⟶ Sp R)
    (c : Fin n → R) (t : Fin n → L.Sec) (φ : Y ⟶ X) (q : (L.pull φ).ι) :
    (GlobalTheory.Cartier.secPull (∑ j, GlobalTheory.AbLaw.cst p ⊤ (c j) • t j) φ).f q =
      ∑ j, GlobalTheory.AbLaw.cst (φ ≫ p) ((L.pull φ).U q) (c j) * (GlobalTheory.Cartier.secPull (t j) φ).f q := by
  have hc : ∀ (U : X.Opens) (r : R),
      (φ.app U).hom (GlobalTheory.AbLaw.cst p U r) = GlobalTheory.AbLaw.cst (φ ≫ p) (φ ⁻¹ᵁ U) r := fun U r => by
    rw [Scheme.Hom.app_eq_appLE]
    exact GlobalTheory.LinChange.appLE_cst p φ le_rfl r
  dsimp only [GlobalTheory.Cartier.secPull]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [comb_f, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, hc, GlobalTheory.LinChange.resG_cst]

end GlobalTheory.SpanVA


open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus) in
theorem GlobalTheory.SpanVA.toProj_preimage_nonzeroLocus_lin : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Sp R) (H : LB X) (m N : ℕ) (s : Fin (m + 1) → LB.Sec H) (t : Fin (N + 1) → LB.Sec H) (a : Matrix (Fin (m + 1)) (Fin (N + 1)) R), H.IsLB → ∀ (ht : ⨆ j, nonzeroLocus (t j) = ⊤), (∀ i, s i = ∑ j, GlobalTheory.AbLaw.cst f ⊤ (a i j) • t j) → ∀ i, GlobalTheory.ProjSpace.toProj f t ht ⁻¹ᵁ nonzeroLocus (GlobalTheory.SpanVA.lin a i) = nonzeroLocus (s i) := by
  intro R _ X f H m N s t a hH ht hst i
  rw [← GlobalTheory.Cartier.nonzeroLocus_secPull]
  refine GlobalTheory.Cartier.SecMaps.nonzeroLocus_eq (pull_isLB (GlobalTheory.ProjSpace.O1_isLB R N) _) hH
    (w := GlobalTheory.ProjSpace.toProjIso f t ht) ?_
  rintro ⟨k, q⟩
  have hc := fun j => GlobalTheory.ProjSpace.secMaps_toProjIso f t ht j (k, q)
  change resG X _ ((s i).f k) = _ * resG X _ ((GlobalTheory.Cartier.secPull (GlobalTheory.SpanVA.lin a i) (GlobalTheory.ProjSpace.toProj f t ht)).f q)
  rw [GlobalTheory.SpanVA.lin]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hst i, GlobalTheory.SpanVA.comb_f, GlobalTheory.SpanVA.secPull_comb_f, map_sum, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, map_mul, GlobalTheory.LinChange.resG_cst, GlobalTheory.LinChange.resG_cst, hc j, GlobalTheory.ProjSpace.toProj_str]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyCartierOfLocallyPrincipal
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS

namespace GlobalTheory.CompHS

theorem nonempty_cartier_of_locally_principal : ∀ (Y : Scheme.{0}) (I : Y.IdealSheafData),
    (∀ y : Y, ∃ (W : Y.affineOpens) (a : Γ(Y, W.1)), y ∈ W.1 ∧ a ∈ nonZeroDivisors Γ(Y, W.1) ∧
      I.ideal W = Ideal.span {a}) → Nonempty (Cartier I) := by
  intro Y I h
  obtain ⟨D, hD⟩ := GlobalTheory.EffCartierData.exists_idealSheaf_eq (I := I) h
  have hLB : D.lb.IsLB := by
    refine { cover := D.cover, g_self := ?_, cocycle := ?_ }
    · intro i
      exact Units.ext (D.eq_trans_on i i le_rfl le_rfl (c := 1) (one_mul _).symm).symm
    · intro i j k
      have hi : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U i := inf_le_left.trans inf_le_left
      have hj : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U j := inf_le_left.trans inf_le_right
      have hk : D.U i ⊓ D.U j ⊓ D.U k ≤ D.U k := inf_le_right
      refine Units.ext (D.eq_trans_on i k hi hk ?_)
      rw [D.trans_spec_on i j hi hj, D.trans_spec_on j k hj hk, ← mul_assoc]
      rfl
  refine ⟨{ P := D.lb, isLB := hLB, t := D.canonical, reg := fun i y hi => ?_, cut := ?_ }⟩
  · exact GlobalTheory.Cartier.isRegularFn_iff_germ.1 (D.regular i) y hi
  · refine ideal_ext_stalk fun y => ?_
    obtain ⟨i, hi⟩ := D.exists_mem y
    rw [stalkId_cutIdeal hLB _ i y hi, ← hD, D.stalkId_idealSheaf i y hi, Set.range_const]
    rfl

end GlobalTheory.CompHS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedFamilyNormBoundAbsoluteConstant
section
noncomputable section
namespace GlobalTheory.ColNorms.FamilyBound
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity GlobalTheory.ColNorms

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

theorem genusOne_meanSquare_forms_agree (Λ : AddSubgroup ℂ) (G : ℂ → ℂ) : StandardLatticesGL3.nrm1Sq Λ G = GL3Theta.normSq1 Λ G :=
  (GlobalTheory.Glob.normSq1_eq_nrm1Sq Λ G).symm

theorem conj_normSq (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ))
    {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : admitted D N N' L L') (M : IntermediateField ℚ ℂ) (hD : DataIn D (tor0 D cc δ) M)
    (hcoef : CoefIn D (B.eNat χ N N' L L') M) (ρ : M →ₐ[ℚ] ℂ) {t : ℂ}
    (hT : GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t) :
    normSq D (torConj D (tor0 D cc δ) M ρ) (La D (torConj D (tor0 D cc δ) M ρ) L L') (fnConj D M ρ (B.eNat χ N N' L L')) =
      GL3Theta.normSq1 (lamConj M ρ (lamOf D cc δ)) (GL3Theta.th0 (lamConj M ρ (lamOf D cc δ)) t) ^ (fF D * N * N') := by
  rw [(GlobalTheory.ConjNorm.useNorm_all D cc δ hc _ B.t0 N N' L L' (StandardLatticesGL3.admissible_self_dual_even hA).1 (StandardLatticesGL3.admissible_self_dual_even hA).2.1 (StandardLatticesGL3.admissible_self_dual_even hA).2.2 _
    (ht _ B.t0 N N' L L' hA) M ρ hD hcoef t hT).1, genusOne_meanSquare_forms_agree]

theorem conj_indep (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ) (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) :
    ThetaNormConjugateIndependent D (tor0 D cc δ) (B.eNat χ) := by
  intro N N' L₁ L₁' L₂ L₂' a₁ a₂ M _ hD c₁ c₂ ρ
  have : NumberField M := NumberField.mk
  obtain ⟨t, hT⟩ := GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  rw [conj_normSq B χ hc ht a₁ M hD c₁ ρ hT, conj_normSq B χ hc ht a₂ M hD c₂ ρ hT]

theorem mean_le_of {C : ℝ} (hC : GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) (B : Base D cc δ) (χ : IdE D → ℂ) (hc : StandardLatticesGL3.Crv D cc δ)
    (ht : StandardLatticesGL3.natTie D cc δ (B.eNat χ)) : ThetaMeanBound D (tor0 D cc δ) C (B.eNat χ) := by
  intro Lsc hL N N' L L' hA M _ hD hcoef
  have : NumberField M := NumberField.mk
  have hex : ∀ ρ : M →ₐ[ℚ] ℂ, ∃ t, GL3Theta.IsTwoTorsionPointUnkilled D (lamConj M ρ (lamOf D cc δ)) t := fun ρ => GlobalTheory.Glob.exists_isThetaZero hc hD ρ
  choose t hT using hex
  have hm := hC cc δ M t ⟨hc.1, hc.2, hD, hT⟩ Lsc hL
  have key : meanLogNormSq D (tor0 D cc δ) L L' M (B.eNat χ N N' L L') =
      ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t := by
    unfold meanLogNormSq GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.conjNormSq
    simp_rw [fun ρ => conj_normSq B χ hc ht hA M hD hcoef ρ (hT ρ), Real.log_pow]
    rw [← Finset.mul_sum, mul_div_assoc]
    rfl
  rw [key]
  calc ((fF D * N * N' : ℕ) : ℝ) * GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.meanLog M (lamOf D cc δ) t
      ≤ ((fF D * N * N' : ℕ) : ℝ) * (C * Lsc) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = C * (fF D : ℝ) * (N : ℝ) * (N' : ℝ) * Lsc := by push_cast; ring

theorem familyNorms_of (hT : FamilyTie) (hM : ∃ C : ℝ, 0 ≤ C ∧ ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.SignedLogMeans.MeanLeC C D) : FamilyNorms := by
  obtain ⟨C, -, hC⟩ := hM
  refine ⟨C, fun D cc δ B χ h1 h2 hcc hδ hχ hY => ?_⟩
  have ht := hT D cc δ B χ h1 h2 hcc hδ hχ hY
  have hc : StandardLatticesGL3.Crv D cc δ := ⟨hcc, hδ⟩
  have h14 := theta_link_holds D cc hcc δ hδ B (Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.SO.stdOK B hcc hδ) χ hχ
  exact ⟨h14.1, mean_le_of (hC D) B χ hc ht, conj_indep B χ hc ht, h14.2⟩

theorem familyNorms : FamilyNorms := familyNorms_of _root_.GlobalTheory.FamilyTieProof.familyTie _root_.GlobalTheory.Theta0MeanLeC.theta0MeanLeC

end GlobalTheory.ColNorms.FamilyBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalisedImageHeightUniqueFrame
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.HermTools GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.ChowHt GlobalTheory.TangentOrigin
open GlobalTheory.IndefiniteRowSideFullHecke.RadicalPowers
open GlobalTheory.HSCore GlobalTheory.QCoh
open GlobalTheory
open Formalism.L2.Pj Formalism.NormVectorIdentities.Items

namespace GlobalTheory.ImageHeightFrame

theorem isImageHeight_unique : Quoted → ∀ (F : Type) [Field F] [NumberField F] (V Ω : Type) [AddCommGroup V] [Module F V] [Module (𝓞 F) V] [IsScalarTower (𝓞 F) F V] [Field Ω] [Algebra F Ω] (Nm : (F →+* ℂ) → V → ℝ) (W : Submodule (𝓞 F) V) (ev : V →ₗ[F] Ω) (D : ℕ) (h h' : ℝ), IsTotallyComplex F → CompHt.IsImageHeight Nm W ev D h → CompHt.IsImageHeight Nm W ev D h' → h = h' :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hh hh' => ImageHeightUnique.isImageHeight_unique hh hh'

end GlobalTheory.ImageHeightFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpan
section
noncomputable section

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta CategoryTheory

namespace GlobalTheory.DlogSpan

theorem ker_finite_free {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {h : ℕ}
    (b : (Fin h → O) →ₗ[O] (Fin h → O)) :
    Module.Finite O (LinearMap.ker b) ∧ Module.Free O (LinearMap.ker b) := by
  have flat : ∀ S : Submodule O (Fin h → O), Module.Flat O S := fun S => by
    rw [Module.Flat.flat_iff_torsion_eq_bot_of_isBezout, eq_bot_iff]
    rintro x ⟨a, ha⟩
    have h1 : (a : O) • (x : Fin h → O) = 0 := congrArg Subtype.val ha
    rw [Submodule.mem_bot]
    apply Subtype.ext
    exact (smul_eq_zero.1 h1).resolve_left (nonZeroDivisors.ne_zero a.2)
  haveI := flat (LinearMap.range b)
  haveI : Module.Free O (LinearMap.range b) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property b.rangeRestrict LinearMap.id
    b.surjective_rangeRestrict
  have hs' : ∀ y, b (s y) = y := fun y => congrArg Subtype.val (LinearMap.congr_fun hs y)
  let π : (Fin h → O) →ₗ[O] LinearMap.ker b :=
    (LinearMap.id - s ∘ₗ b.rangeRestrict).codRestrict _ fun x => by
      simp [LinearMap.mem_ker, hs']
  have hπ : Function.Surjective π := fun x => ⟨x, by
    apply Subtype.ext
    have h0 : b.rangeRestrict x = 0 := Subtype.ext x.2
    simp [π, h0]⟩
  haveI hfin : Module.Finite O (LinearMap.ker b) := Module.Finite.of_surjective π hπ
  haveI := flat (LinearMap.ker b)
  exact ⟨hfin, Module.free_of_flat_of_isLocalRing⟩

theorem sub_one_dvd {O : Type} [CommRing O] [IsDomain O] {ζ : O} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ k) (hk : 1 < k) : ζ - 1 ∣ (k : O) := by
  have h0 := hζ.geom_sum_eq_zero hk
  have h1 : (k : O) = -∑ i ∈ Finset.range k, (ζ ^ i - 1) := by
    rw [Finset.sum_sub_distrib, h0]; simp
  rw [h1, dvd_neg]
  exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one ζ i

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

def pDivGroupOmegaBidualEquiv (G : PDivGroup p O) : G.omega ≃ₗ[O] G.dual.dual.omega :=
  LinearEquiv.ofLinear (omegaMap _ _ G.bidual.inv) (omegaMap _ _ G.bidual.hom)
    (by rw [← omegaMap_comp, Iso.inv_hom_id, omegaMap_id])
    (by rw [← omegaMap_comp, Iso.hom_inv_id, omegaMap_id])

theorem pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate (G : PDivGroup p O) (χ : G.dual.Tate) :
    pDivGroupOmegaBidualEquiv G (dlog G χ) = hodgeTate G.dual χ := by
  rw [hodgeTate_apply, ← dualHom_bidual_inv, dlog_tateMap]
  rfl

theorem finite_free_and_sq_smul_mem_span : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O] (ε : PreTilt O p) (hε : GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.IsPrimitiveSystem ε), v.Integers O → GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta.HodgeTateSandwichAt hε → ∀ G : PDivGroup p O, Module.Finite O G.omega ∧ Module.Free O G.omega ∧ ∀ w : G.omega, (p : O) ^ 2 • w ∈ Submodule.span O (Set.range (dlog (G := G))) := by
  intro p hp C _ _ _ v O _ _ _ _ _ ε hε hv hS G
  haveI : ValuationRing O := ValuationRing.of_integers v hv
  obtain ⟨u₁, u₂, hS⟩ := hS
  obtain ⟨D, e, fil, lie, hR⟩ := hS G.dual ℤ_[p] (padicAction _)
  let Ψ : G.omega ≃ₗ[O] D.Fil := pDivGroupOmegaBidualEquiv G ≪≫ₗ fil
  obtain ⟨hfin, hfree⟩ := ker_finite_free D.bb
  haveI : Module.Finite O D.Fil := hfin
  haveI : Module.Free O D.Fil := hfree
  refine ⟨Module.Finite.equiv Ψ.symm, Module.Free.of_equiv Ψ.symm, fun w => ?_⟩
  have hζ : IsPrimitiveRoot (root ε).untilt p := by
    have h := hε 1
    rw [pow_one] at h
    exact h
  obtain ⟨-, -, -, hb, -⟩ := HodgeTateBound.bound p C v O hv ε hζ ℤ_[p] _ D
  have hθ : WittVector.fontaineTheta O p (nu ε) = (root ε).untilt - 1 := by
    rw [nu, map_sub, WittVector.fontaineTheta_teichmuller, map_one]
  have hal : ∀ χ : G.dual.Tate, D.al (toO e χ) = (Ψ ((u₁ : O) • dlog G χ) : Fin _ → O) := by
    intro χ
    rw [hR.al_eq, ← hodgeTate_eq_omegaMap, ← pDivGroupOmegaBidual_dlog_eq_dual_hodgeTate, map_smul]
    rfl
  have key : ∀ y, ∃ s ∈ Submodule.span O (Set.range (dlog G)),
      D.al y = (Ψ s : Fin _ → O) := by
    intro y
    refine ⟨∑ i, y i • (u₁ : O) • dlog G (e.symm (Pi.single i 1)), ?_, ?_⟩
    · exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩))
    · have hy : y = ∑ i, y i • toO e (e.symm (Pi.single i 1)) := by
        ext j
        simp [toO, Finset.sum_apply, Pi.single_apply, apply_ite]
      conv_lhs => rw [hy]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_sum, Submodule.coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hal, map_smul Ψ (y i), Submodule.coe_smul]
  obtain ⟨y, hy⟩ := hb (Ψ w) (Ψ w).2
  obtain ⟨s, hs, hys⟩ := key y
  have h1 : WittVector.fontaineTheta O p (nu ε) • w = s := by
    apply Ψ.injective
    apply Subtype.ext
    rw [map_smul, Submodule.coe_smul, ← hy, hys]
  obtain ⟨c, hc⟩ := sub_one_dvd hζ hp.out.one_lt
  have h2 : (p : O) ^ 2 • w = ((p : O) * c) • s := by
    rw [← h1, hθ, smul_smul, pow_two]
    congr 1
    rw [mul_assoc, mul_comm c, ← hc]
  rw [h2]
  exact Submodule.smul_mem _ _ hs

end GlobalTheory.DlogSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrimeSpectrumDualNumberEq
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompHS

open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.TopForm GlobalTheory.Adelic GlobalTheory.TangentOrigin
open GlobalTheory.FlagTan (IsDef)

theorem exists_isFreeGen_dForm {k A : Type} [CommRing k] [CommRing A] {α : k →+* A} {D : ℕ}
    (h : α.IsStandardSmoothOfRelativeDimension D) : ∃ f : Fin D → A, IsFreeGen A (dForm α f) := by
  classical
  letI := α.toAlgebra
  haveI : Algebra.IsStandardSmoothOfRelativeDimension D k A := h
  obtain ⟨ι, σ, _, _, P, hP⟩ := ‹Algebra.IsStandardSmoothOfRelativeDimension D k A›.out
  letI := Fintype.ofFinite ι
  letI := Fintype.ofFinite σ
  have hc : Fintype.card ((Set.range P.map)ᶜ : Set ι) = D := by
    rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP]
    simp [Algebra.Presentation.dimension]
  let e := Fintype.equivFinOfCardEq hc
  exact ⟨fun i => P.val (e.symm i), isFreeGen_dForm _ (P.basisKaehler.reindex e) fun i => by
    simp⟩

theorem exists_isFrame_dOn {k : Type} [CommRing k] {Y : Scheme.{0}} (p : Y ⟶ Sp k) (D : ℕ)
    [SmoothOfRelativeDimension D p] (x : Y) :
    ∃ (U : Y.Opens) (f : Fin D → Γ(Y, U)), x ∈ U ∧ IsFrame (dOn p f) := by
  obtain ⟨V, hV, hx, -⟩ := Opens.isBasis_iff_nbhd.1 Y.isBasis_affineOpens (Opens.mem_top x)
  have h := HasRingHomProperty.appLE (@SmoothOfRelativeDimension D) p ‹_›
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, h⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h
  obtain ⟨t, hxt⟩ : ∃ t : (s : Set Γ(Y, V)), x ∈ Y.basicOpen (t : Γ(Y, V)) :=
    Opens.mem_iSup.1 (((IsAffineOpen.iSup_basicOpen_eq_self_iff hV).2 hs).ge hx)
  have := IsAffineOpen.isLocalization_basicOpen hV (t : Γ(Y, V))
  have h₁ := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2 _
    (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv
    (h t t.2 Γ(Y, Y.basicOpen (t : Γ(Y, V))))
  have h₂ : (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p (Y.basicOpen (t : Γ(Y, V)))).IsStandardSmoothOfRelativeDimension D := by
    rw [← resG_comp_algX p (Y.basicOpen_le (t : Γ(Y, V)))]
    exact h₁
  obtain ⟨f, hf⟩ := exists_isFreeGen_dForm h₂
  exact ⟨_, f, hxt, IsAffineOpen.basicOpen hV _, hf⟩

theorem primeSpectrum_dualNumber_eq {L : Type} [Field L] (x y : PrimeSpectrum (DualNumber L)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber L), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem le_preimage_of_dualNumber {L : Type} [Field L] {T : Scheme.{0}} (φ : DualNumber L →+* L)
    (x : Sp (DualNumber L) ⟶ T) (V : T.Opens) (h : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ V) : ⊤ ≤ x ⁻¹ᵁ V := by
  intro s _
  have hp : (spMap φ) (IsLocalRing.closedPoint L) = s := primeSpectrum_dualNumber_eq _ _
  have h₁ : (spMap φ ≫ x) (IsLocalRing.closedPoint L) ∈ V := h (Set.mem_univ _)
  exact hp ▸ h₁

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {X : GlobalTheory.FlagMod.FlagCover Y} {Z : Comp Xo c}
  (M : Modif (str₀ X Z) (U₀ X Z) (GlobalTheory.FlagTan.dimFlag Dw))

theorem exists_tanLift {L : Type} [Field L] [Algebra c.F L] {Q : FrPt Xo c L} {v : FrPt Xo c (DualNumber L)}
    (hd : IsDef Q v) {z : Sp L ⟶ M.X} (hz : z ≫ toFlag M = X.ptY Q) (ho : ⊤ ≤ z ⁻¹ᵁ M.off) :
    ∃ zv : Sp (DualNumber L) ⟶ M.X, zv ≫ toFlag M = X.ptY v ∧ ∀ O : M.X.Opens, ⊤ ≤ z ⁻¹ᵁ O → ⊤ ≤ zv ⁻¹ᵁ O := by
  have e := (X.ptY_frMap hd).trans hz.symm
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ X Z := fun s _ => by
    have := ho (Set.mem_univ s)
    rw [M.off_eq] at this
    exact this
  have hb : ⊤ ≤ X.ptY v ⁻¹ᵁ (inc₀ X Z).opensRange := le_preimage_of_dualNumber _ _ _ (by
    rw [e]
    rintro s -
    exact ⟨(z ≫ M.σ) s, rfl⟩)
  have hr : Set.range (X.ptY v) ⊆ Set.range (inc₀ X Z) := by
    rintro _ ⟨s, rfl⟩
    exact hb (Set.mem_univ s)
  obtain ⟨w, hw⟩ : ∃ w, w ≫ inc₀ X Z = X.ptY v := ⟨_, IsOpenImmersion.lift_fac _ _ hr⟩
  have ered : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ w = z ≫ M.σ := by
    rw [← cancel_mono (inc₀ X Z), Category.assoc, hw, e, Category.assoc]
  have hwU : ⊤ ≤ w ⁻¹ᵁ U₀ X Z := le_preimage_of_dualNumber _ _ _ (by rw [ered]; exact hU)
  obtain ⟨zv, hzv, -⟩ := M.existsUnique_lift w hwU
  have hred : spMap (GlobalTheory.FlagTan.red c L).toRingHom ≫ zv = z :=
    (M.existsUnique_lift (z ≫ M.σ) hU).unique (by rw [Category.assoc, hzv, ered]) rfl
  refine ⟨zv, ?_, fun O hO => le_preimage_of_dualNumber _ _ _ (by rw [hred]; exact hO)⟩
  rw [toFlag, ← Category.assoc, hzv, hw]

end GlobalTheory.CompHS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatDarbouxCoordsRationalMatrixIffRatPairStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ratDarbouxCoords_rationalMatrix_iff_ratPair : ∀ (D : D7) (S T : HSp D) (κ : Type) [Fintype κ]
    (e : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)) ≃ₗ[AF D.host.F]
      (κ → AF D.host.F) × (κ → AF D.host.F)),
    (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
      e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
    ∀ w : Matrix (Fin T.rank) (Fin S.rank) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := D.host.F) (E := D.host.E)),
      w ∈ ratL T S ↔ e w ∈ GlobalTheory.WeilUnitaryTransport.ratPair D.host.F κ := by
  first | exact @GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair | exact GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair | (intros; apply GlobalTheory.RatDarbouxPointsD.ratL_iff_ratPair <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaTransformDoubledTargetBoxProductStatement
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaTransform_doubledTarget_boxProduct : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → Formalism.IndefR.DatumF.IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JT JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E)
      (hA : JA = JTᵀ) (κ : Type) [Fintype κ] (co : Darboux (symp (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) ξ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JA) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) JB)) κ),
      ∀ φ₁ ∈ schA F κ, ∀ φ₂ ∈ schA F κ,
        GlobalTheory.WeilSchrodinger.thetaTr F (GlobalTheory.WeilSchrodinger.DblTargetF.coDbl hA co) B.ψ (boxFun φ₁ φ₂) =
          GlobalTheory.DblTargetDelta.deltaT (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ φ₁)
            (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (fun x => starRingEnd ℂ (φ₂ (-x)))) := by
  first | exact @GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun | exact GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun | (intros; apply GlobalTheory.DblThetaProd.thetaTr_coDbl_boxFun <;> assumption)
end

