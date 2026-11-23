module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0030
public import Formalism.LocalToGlobal.KernelLattices.TopPin
public import Formalism.LocalToGlobal.KernelLattices.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0389
public import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0400
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0472
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocGen
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0425
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0417
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0442
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaFixedDvdValuationOrder
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.Member.TameDivOrd

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma ord_vw_unit_mul_uniformiser_pow {W : Type} [CommRing W] [IsDomain W]
    [IsDiscreteValuationRing W] {ϖ : W} (hϖ : Irreducible ϖ) (h0 : ϖ ≠ 0) (u : Wˣ) (m : ℕ) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun
      (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m) = m := by
  induction m with
  | zero =>
    rw [pow_zero, _root_.mul_one, Nat.cast_zero]
    exact (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).map_unit u
  | succ m ih =>
    rw [pow_succ, ← _root_.mul_assoc, _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul, ih,
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw_uniformiser h0
        ((IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ)]
    push_cast
    ring

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma eq_one_of_pow_eq_one_of_ne_zero {Γ : Type*} [LinearOrderedCommGroupWithZero Γ] {a : Γ}
    {k : ℕ} (hk : k ≠ 0) (h : a ^ k = 1) : a = 1 := by
  rcases lt_trichotomy a 1 with h1 | h1 | h1
  · exact absurd h (pow_lt_one₀ zero_le' h1 hk).ne
  · exact h1
  · exact absurd h (one_lt_pow₀ h1 hk).ne'

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
private lemma one_le_valuation_root_of_unity_sub_one {F : Type} [Field F] (O : ValuationSubring F) {k : ℕ}
    (hk : IsUnit (k : O)) {w : F} (hw : w ^ k = 1) (hw1 : w ≠ 1) : 1 ≤ O.valuation (w - 1) := by
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have hsum : ∑ i ∈ Finset.range k, w ^ i = 0 := by
    rw [geom_sum_eq hw1, hw, sub_self, zero_div]
  have hkF : (k : F) = (w - 1) * -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j := by
    rw [mul_neg, Finset.mul_sum]
    simp_rw [mul_comm (w - 1), geom_sum_mul]
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hvw : O.valuation w = 1 :=
    eq_one_of_pow_eq_one_of_ne_zero hk0 (by rw [← map_pow, hw, map_one])
  have hwO : w ∈ O := (O.valuation_le_one_iff w).1 hvw.le
  have hcO : -∑ i ∈ Finset.range k, ∑ j ∈ Finset.range i, w ^ j ∈ O :=
    neg_mem (sum_mem fun i _ => sum_mem fun j _ => pow_mem hwO j)
  have hvk : O.valuation (k : F) = 1 := by
    simpa using O.valuation_unit hk.unit
  rw [← hvk, hkF, map_mul]
  exact mul_le_of_le_one_right' ((O.valuation_le_one_iff _).2 hcO)


open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory.Limits _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing in
open scoped CategoryTheory.Obj in
set_option autoImplicit false in
theorem _root_.GlobalTheory.Member.TameDivOrd.tame_fixed_dvd_ord : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ (k : ℕ) (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F), IsUnit (k : O) →
      IsLocalHom φ → (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) →
      (∀ x ∈ O, O.valuation (σ x - x) < 1) → π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) →
      IsPrimitiveRoot (σ π / π) k →
      ∀ (d : F) (z : (FractionRing W)ˣ), σ d = d → O.valuation d ^ k = O.valuation (algebraMap (FractionRing W) F z) →
        (k : ℤ) ∣ (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z := by
  intro W _ _ _ F _ _ ϖ hϖ k O φ σ π hk _ hφ hσ hπ hζ d z hd hdz
  have hk0 : k ≠ 0 := by
    rintro rfl
    simp at hk
  have h0 : ϖ ≠ 0 := hϖ.ne_zero
  have hϖF : algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ≠ 0 :=
    (map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective W (FractionRing W))).2 h0)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0] at hπ
    exact hϖF hπ.symm
  set ζ := σ π / π with hζdef
  have hσπ : σ π = ζ * π := by rw [hζdef, div_mul_cancel₀ _ hπ0]
  obtain ⟨a, b, hb, hab⟩ := IsFractionRing.div_surjective W (z : FractionRing W)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbF : algebraMap W (FractionRing W) b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have key : (z : FractionRing W) * algebraMap W _ b = algebraMap W _ a := by
    rw [← hab, div_mul_cancel₀ _ hbF]
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at key
    exact z.ne_zero (by simpa [hbF] using key)
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hϖ
  obtain ⟨m', u', rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ

  have hU : z * (Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u' *
      _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m') =
      Units.map (algebraMap W (FractionRing W) : W →* FractionRing W) u *
        _root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 ^ m := by
    ext
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [show ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.toUnitK ϖ h0 : (FractionRing W)ˣ) : FractionRing W) =
      algebraMap W _ ϖ from rfl, ← map_pow, ← map_mul, ← map_pow, ← map_mul, key]
  have hord : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z + m' = m := by
    have := congrArg (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun hU
    rwa [_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.LatticeVal.map_mul,
      ord_vw_unit_mul_uniformiser_pow hϖ, ord_vw_unit_mul_uniformiser_pow hϖ] at this

  have hφu : ∀ x : Wˣ, O.valuation (φ x : F) = 1 := fun x => by
    simpa using O.valuation_unit (Units.map (φ : W →* O) x)
  have keyF : algebraMap _ F (z : FractionRing W) * ((φ u' : F) * (φ ϖ : F) ^ m') =
      (φ u : F) * (φ ϖ : F) ^ m := by
    have := congrArg (algebraMap (FractionRing W) F) key
    simpa only [hφ, map_mul, map_pow] using this
  have hP : O.valuation (φ ϖ : F) = O.valuation π ^ k := by rw [hφ, ← hπ, map_pow]
  have hV : O.valuation d ^ k * O.valuation π ^ (k * m') = O.valuation π ^ (k * m) := by
    have := congrArg O.valuation keyF
    simp only [map_mul, map_pow, hφu, _root_.one_mul, hP] at this
    rw [hdz, pow_mul, pow_mul]
    exact this
  have hvπ : O.valuation π ≠ 0 := (Valuation.ne_zero_iff _).2 hπ0
  set y := d * π ^ m' / π ^ m with hydef
  have hvy : O.valuation y = 1 := by
    apply eq_one_of_pow_eq_one_of_ne_zero hk0
    rw [hydef, map_div₀, map_mul, map_pow, map_pow, div_pow, mul_pow, ← pow_mul, ← pow_mul,
      mul_comm m' k, mul_comm m k, hV, div_self (pow_ne_zero _ hvπ)]
  set w := ζ ^ m' / ζ ^ m with hwdef
  have hσy : σ y = w * y := by
    rw [hydef, hwdef, map_div₀, map_mul, map_pow, map_pow, hd, hσπ]
    ring
  have hyO : y ∈ O := (O.valuation_le_one_iff y).1 hvy.le
  have hwk : w ^ k = 1 := by
    rw [hwdef, div_pow, ← pow_mul, ← pow_mul, mul_comm m' k, mul_comm m k, pow_mul, pow_mul,
      hζ.pow_eq_one, one_pow, one_pow, div_one]
  have hw : w = 1 := by
    by_contra hw1
    have h1 := one_le_valuation_root_of_unity_sub_one O hk hwk hw1
    have hlt := hσ y hyO
    rw [hσy, show w * y - y = (w - 1) * y by ring, map_mul, hvy, _root_.mul_one] at hlt
    exact absurd hlt (not_lt.2 h1)
  have hdvd : (k : ℤ) ∣ (m' : ℤ) - m := by
    rw [← hζ.zpow_eq_one_iff_dvd, zpow_sub₀ (hζ.ne_zero hk0), zpow_natCast, zpow_natCast]
    exact hw
  have hn : (_root_.GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.ord_vw W).toFun z = m - m' := by omega
  rw [hn, ← dvd_neg, neg_sub]
  exact hdvd

end GlobalTheory.Member.TameDivOrd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueChainsKernelDatumSourceSideLattice
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000

namespace GlobalTheory.KerLatS

theorem charts_read_step {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hPins : TC.Pins B X) (l : I.Laws)
    (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (him : i < B.R.m) :
    ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch)
      (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K := by
  classical
  rcases Nat.eq_zero_or_pos i with rfl | h1
  · exact GlobalTheory.T.exists_charts_reading_step_zero I hOk hPins l Z u a
  · obtain ⟨Ch0, _, chOf0, K0, hK0, -⟩ := GlobalTheory.T.exists_memberStep_charts I hOk hPins l Z u i hi
    obtain ⟨Ch, _, chOf, K, -, hK, -⟩ := GlobalTheory.T.tupleChain_middleStage_charts_joined_member I hOk hPins l Z u a ((I.Q a).image fun P => P.under (𝓞 B.host.F)) i hi
      Ch0 chOf0 K0 h1 him (fun v => Finset.mem_image) hK0
    exact ⟨_, Ch, chOf, K, hK⟩

theorem kerEntHyp_latS : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (l0 : I.Law0 l) (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z)) (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs → (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) → (∀ u a i, i < B.R.m → UnfIsAll (O u a) i) → ColIn.JetsIn I → ∀ u μ w, LevFree Y u μ w → ∀ i, i < (I.rec7 l Z).R.m → ∀ φ : ((I.rec7 l Z).chTw u μ).cls i → ((I.rec7 l Z).chTw u μ).Y i → ℂ, (∃ x ∈ locW (I.rec7 l Z).what₂.places w (((I.tw l l0 Z).fm u μ).lat i).L, ((I.tw l l0 Z).fm u μ).emb i x = φ) ↔ (φ ∈ ((I.tw l l0 Z).fm u μ).Fi i ∧ ∀ c, ∃ v : ValQ O u μ i, evC O u μ i v = φ c ∧ ∀ J : KM.ColChoice ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i), ‖prSC Pl O Bs u μ w i c v (MvPolynomial.map (Int.castRingHom _) (KM.nablaX ((I.rec7 l Z).R.N i) (nuD (I.rec7 l Z) u i) J))‖ ≤ 1) := by
  intro B X I hOk hPins l Z l0 Y O Pl Bs hQp hStd hBas hEnt _hUnf _hJets u μ w hw i hi φ
  obtain ⟨bad, Ch, chOf, K, hK⟩ := charts_read_step I hOk hPins l Z u μ i hi.le hi
  have hY : I.IdY l Z u μ i hi.le (Equiv.refl _) := fun _ => rfl
  have V := GlobalTheory.T.hermitianChart_complex_rational_integral_forms I hOk hPins l Z u μ i hi.le bad Ch chOf K (Equiv.refl _) hK hY
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hrat := (V.rat ((I.fm l u μ).emb i x)).1 ⟨x, rfl⟩
    have hlat := (V.lat w trivial x).1 hx
    refine ⟨hrat.1, fun c => ?_⟩
    obtain ⟨Bm, hBm⟩ := Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.LocB.exists_isLocBasis ((I.rec7 l Z).what₂.places.resChar w) _ _
      ((I.stp u μ i).rep c).1.1.deco.2.lat.fg (by
        open Formalism.HermitianLatticesTheory Module in
        let L := ((I.stp u μ i).rep c).1.1.deco.1.N
        have hL := ((I.stp u μ i).rep c).1.1.deco.2.lat
        have hu : IsUnimodular (Formalism.L2.Col.hStd B.fields.E (B.R.N i)) L :=
          ((I.stp u μ i).rep c).1.1.deco.2.uni
        let W := Submodule.span B.fields.E (L : Set (Sp B.fields.E (B.R.N i)))
        change W = ⊤
        by_contra h
        let e : Sp B.fields.E (B.R.N i) ≃ₗ⋆[B.fields.E] Sp B.fields.E (B.R.N i) := starLinearEquiv B.fields.E
        let g : Sp B.fields.E (B.R.N i) →ₗ[B.fields.E] Module.Dual B.fields.E W :=
          (LinearMap.domRestrict' W).comp ((Formalism.L2.Col.hStd B.fields.E (B.R.N i)).comp e.toLinearMap)
        have hdim : finrank B.fields.E (Module.Dual B.fields.E W) <
            finrank B.fields.E (Sp B.fields.E (B.R.N i)) := by
          rw [Subspace.dual_finrank_eq]
          exact Submodule.finrank_lt h
        obtain ⟨x, hx, hx₀⟩ :=
          Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
        have hsmul (a : B.fields.E) : a • e x ∈ L := by
          rw [← hu, dualBasic_mem_dual]
          intro y hy
          apply hStd_mem_one_symm
          have hxy : Formalism.L2.Col.hStd B.fields.E (B.R.N i) (e x) y = 0 :=
            congrArg (fun f : Module.Dual B.fields.E W => f ⟨y, Submodule.subset_span hy⟩)
              (LinearMap.mem_ker.mp hx)
          simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
        let j : B.fields.E →ₗ[𝓞 B.fields.E] L :=
          ((LinearMap.toSpanSingleton B.fields.E _ (e x)).restrictScalars (𝓞 B.fields.E)).codRestrict L hsmul
        let : Module.Finite (𝓞 B.fields.E) L := Module.Finite.iff_fg.mpr hL.fg
        let : Module.Finite (𝓞 B.fields.E) B.fields.E := Module.Finite.of_injective j fun a b hab =>
          smul_left_injective B.fields.E (fun hz => hx₀ (e.map_eq_zero_iff.mp hz)) (congrArg Subtype.val hab)
        exact RingOfIntegers.not_isField B.fields.E
          (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 B.fields.E) B.fields.E) (Field.toIsField B.fields.E)))
    have hBm' := (_root_.GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N I hOk hPins l Z Y u μ w hw i hi.le c Bm).2 hBm
    exact (_root_.GlobalTheory.LatSCore.latS_at_class I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat.2 c) Bm
      hBm).1 (hlat c Bm hBm')
  · rintro ⟨hFi, hc⟩
    have hrat : ∀ c, ∃ P ∈ Formalism.L2.Forms.RatSpan (I.rec7 l Z) ((I.fm l u μ).lam i), ∀ z, φ c z =
        fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P
          ((Equiv.refl _) z) := by
      intro c
      obtain ⟨v, hv, -⟩ := hc c
      rw [← hv]
      exact _root_.GlobalTheory.KerValRat.evC_ratSpan I hOk hPins l Z Y O hQp hStd u μ i hi (Equiv.refl _) hY v
    obtain ⟨x, hx⟩ := (V.rat φ).2 ⟨hFi, hrat⟩
    refine ⟨x, (V.lat w trivial x).2 fun c Bm hBm => ?_, hx⟩
    have hBm' := (_root_.GlobalTheory.DualOffLevel.isLocBasis_dual_iff_N I hOk hPins l Z Y u μ w hw i hi.le c Bm).1 hBm
    have h1 := (_root_.GlobalTheory.LatSCore.latS_at_class I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hw i hi (Equiv.refl _) hY c _ (hrat c) Bm
      hBm').2 (hc c)
    rw [hx]
    exact h1

end GlobalTheory.KerLatS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypePrimeFiniteGroupEqExtendedData
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

theorem GlobalTheory.Mem.R3.DefLatBC.typePrimeFiniteGroup_heq_of_eq_preData (B B' : Base) (px : PreX B.toPre) (px' : PreX B'.toPre) (h : B'.toPre = B.toPre) (hp : HEq px' px) :
    ∃ e : Gc B px ≃* Gc B' px', ∀ g, HEq (e g) g := by
  cases B
  cases B'
  dsimp only at h
  subst h
  cases hp
  exact ⟨MulEquiv.refl _, fun g => HEq.rfl⟩

theorem GlobalTheory.Mem.R3.DefLatBC.gc_ext : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ e : Gc B w.px ≃* Gc B' w'.px, ∀ g, HEq (e g) g) := by
  intro _ _ _ _ _ _ _
  refine StepW.of_all fun K B' f' T' w' _ _ _ B f T w hE _ _ hp => ?_
  intros
  exact GlobalTheory.Mem.R3.DefLatBC.typePrimeFiniteGroup_heq_of_eq_preData B B' w.px w'.px hE.1 hp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorusPart

theorem mono_gtTorus_and_factor {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {A : Type}
    [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {ρ : R →+* A} {D : Out.DegPre R} {e : ℕ}
    {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G] {G₀ : Over (Sp A)} [GrpObj G₀]
    {φ : G₀.left ⟶ G.left} (g : Out.GtCoord I D e G) (hρ : ∀ x ∈ I ^ (e + 1), ρ x = 0)
    (h : IsGrpPullback G₀ G (spMap ρ) φ) :
    Mono (gtTorus g hρ h) ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
      (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
        ∃ r : D.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ r ≫ gtTorus g hρ h := by
  have := g.i_hom; have := g.q_hom; have := D.P.isAb.proper
  have : IsProper (Out.thickObj R I e D.P.A).hom := inferInstanceAs (IsProper (pullback.snd _ _))
  obtain ⟨q', hq', hk'⟩ := exists_isKernel_pullTorus (isGrpPullback_thickLift hρ h) g.i g.q g.isKernel
  have hk : IsPullback (gtTorus g hρ h) (toUnit _) q' η[_] := hk'
  have : IsProper ((Over.pullback (thickPt e hρ)).obj (Out.thickObj R I e D.P.A)).hom :=
    inferInstanceAs (IsProper (pullback.snd _ _))
  haveI : ConnectedSpace (Sp A) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing A
  have hm : Mono (gtTorus g hρ h) := ⟨fun a b k => hk.hom_ext k (toUnit_unique _ _)⟩
  refine ⟨hm, fun X _ _ _ i hi => ?_⟩
  haveI := hi; haveI := hq'
  have ht : i ≫ q' = toUnit _ ≫ η[_] :=
    splitTorus_hom_proper_trivial_local A X _ (i ≫ q') inferInstance
  let u := hk.lift i (toUnit _) ht
  have hu : u ≫ gtTorus g hρ h = i := hk.lift_fst _ _ _
  have : IsMonHom u := Serre.isMonHom_of_mul_comp u fun T x y => by
    rw [← cancel_mono (gtTorus g hρ h), MonObj.mul_comp (x ≫ u), Category.assoc, Category.assoc,
      Category.assoc, hu, MonObj.mul_comp]
  obtain ⟨r, hr⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap u
  exact ⟨r, by rw [← hr, hu]⟩

theorem mono_gtTorus_unif_and_factor : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (t : SAB H (Sp R)) (P : PELUnif I t)
    (A : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (a : R →+* A) (e : ℕ) (ha : ∀ x ∈ I ^ (e + 1), a x = 0)
    (G₀ : Over (Sp A)) [GrpObj G₀] (φ : G₀.left ⟶ t.G.left) (h : IsGrpPullback G₀ t.G (spMap a) φ),
    Mono (GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h) ∧
    ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (i : splitTorus (Sp A) X ⟶ G₀), IsMonHom i →
      ∃ ρ : P.D.toPre.X →+ X, i = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (P.U.gt e) ha h := by
  intro E _ _ _ H R _ _ I t P A _ _ _ a e ha G₀ _ φ h
  exact mono_gtTorus_and_factor (P.U.gt e) ha h

end GlobalTheory.TorusPart
end
end

