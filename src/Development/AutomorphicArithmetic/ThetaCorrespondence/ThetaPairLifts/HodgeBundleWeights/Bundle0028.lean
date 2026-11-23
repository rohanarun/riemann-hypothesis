module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2950
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0011
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0009
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0027
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0015
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0023
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1847
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2927
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CuspRatioFieldEqTopOfToroidalCompactification
section
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SepCusp
section Geometry
open CategoryTheory AlgebraicGeometry TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn exOf secZ)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open GlobalTheory.Vanishing.H0
open GlobalTheory.CompHt (genVal genPoint)
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
theorem cuspRatioField_eq_top_of_toroidalCompactification (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hG : GlobalTheory.Published.GrothendieckDeformation) (hN : GlobalTheory.Published.NefNumerics)
    (hSi : GlobalTheory.Published.SiegelToroidalIntegral) (hCh : GlobalTheory.Published.ToroidalChartsForFan)
    (hLie : GlobalTheory.Published.SemiAbelianLieSeminegative) (hS : GlobalTheory.Published.PointSeparationPair) (TF : TorFlag Xo c)
    (Z : Comp Xo c) {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (hF : FnAlgClosed (Xo := Xo) (c := c)) (hD : 1 ≤ dimFlag Dw)
    (hpq : 1 ≤ Dw.p + Dw.q) (la : AllWt.Weight Dw)
    (hg : GapGe (((dimFlag Dw + 2).choose 2 : ℕ) : ℤ) (la - FlagTan.kap Dw))
    (hv : vanBd TF.X Z la ≤ space TF.X Z U la) :
    GlobalTheory.DegVal.ratioField (genPoint Z (cuspOn U Z (wtOf Dw la 0))) = ⊤ := by
  set L := GlobalTheory.DegVal.ratioField (genPoint Z (cuspOn U Z (wtOf Dw la 0))) with hL
  haveI := c.fin
  haveI : Countable c.F := (Module.finBasis ℚ c.F).equivFun.injective.countable
  haveI : Countable (Om Z) := TwoPoint.countable_of_fg c.F (Om Z) ((FlagDim.fnFG_fnTrdeg E H Dw l Xo c).1 Z)
  refine eq_top_iff.2 fun a _ => by_contra fun ha => ?_
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap c.F L).injective
  obtain ⟨i₁, i₂, hi, hne⟩ := TwoPoint.exists_two_embeddings L (Om Z) a (by rintro ⟨b, rfl⟩; exact ha b.2)
  have hag : ∀ b ∈ L, i₁ b = i₂ b := fun b hb => RingHom.congr_fun hi ⟨b, hb⟩
  have hV := GlobalTheory.VarFlag.isVariety₀_flag E H Dw l Xo c TF Z hF
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  haveI : IsAffineHom M.σ := inferInstanceAs (IsAffineHom (𝟙 (Y₀ TF.X Z)))
  have hconn : GeometricallyConnected M.str := by
    have e : M.str = str₀ TF.X Z := Category.id_comp (str₀ TF.X Z)
    rw [e]
    exact hV.2.2
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M
    (fun K _ _ y => _root_.GlobalTheory.FlagTan.kodaira_spencer_iso_flag_tangent_psi_set hP hG E H Dw l Xo c K y hpq)
  obtain ⟨F, hFg⟩ := _root_.GlobalTheory.T.cusp_germ_transfer_of_boundary hP hG E H Dw l Xo c TF Z r U hF M ω (la - FlagTan.kap Dw) la (by abel) hv
  have h : GenFrEx Xo c := (Reg.genFrEx_and_genFromTest E H Dw l Xo c).1
  obtain ⟨z, hz, hO⟩ := exists_lift_genFr M h
  have hzo : ptOf z ∈ M.off := (le_iff_ptOf_mem _ _).1 hO
  have hη : M.σ (ptOf z) ∈ U₀ TF.X Z := M.off_eq.le hzo
  have hU : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ U₀ TF.X Z := (le_iff_ptOf_mem _ _).2 hη
  have hB := LB.isLB_pull (isLB_L₀ TF.X Z (la - FlagTan.kap Dw)) M.σ
  obtain ⟨j, hj⟩ := exists_chart (isLB_tens M.K.isLB hB) (ptOf z)
  have hj' := (le_iff_ptOf_mem z _).2 hj
  obtain ⟨i, hi₀⟩ := exists_chart (isLB_L₀ TF.X Z la) (M.σ (ptOf z))
  have hi' : ⊤ ≤ (z ≫ M.σ) ⁻¹ᵁ (L₀ TF.X Z la).U i := (le_iff_ptOf_mem _ _).2 hi₀
  obtain ⟨u, hu⟩ := hFg (ptOf z) hzo j hj i hi₀
  obtain ⟨T, hT, hTv⟩ := exists_val_cuspSec TF.X Z U la h (z ≫ M.σ) (by rw [Category.assoc]; exact hz) hU i hi'
  obtain ⟨T', hT', hval⟩ : ∃ T' : Om Z, T' ≠ 0 ∧ ∀ g, H0.val z j le_top hj' g = T' * genVal Z (F g).1 := by
    refine ⟨(Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) z).hom u.val * T,
      mul_ne_zero (u.isUnit.map _).ne_zero hT, fun g => ?_⟩
    rw [val_eq_stalk z j le_top hj' (memTop _) hj, hu, mul_assoc, ← hTv,
      val_eq_stalk (z ≫ M.σ) i hU hi' hη hi₀, Scheme.stalkClosedPointTo_comp]
    exact map_mul (Scheme.stalkClosedPointTo (R := CommRingCat.of (Om Z)) z).hom _ _
  let σ : c.F →+* ℂ := i₁.comp (algebraMap c.F (Om Z))
  have hσ : i₂.comp (algebraMap c.F (Om Z)) = σ := RingHom.ext fun k => (hag _ (L.algebraMap_mem k)).symm
  let ι : Fin 2 → (Om Z →+* ℂ) := ![i₁, i₂]
  have hι : ∀ n, (ι n).comp (algebraMap c.F (Om Z)) = σ := Fin.forall_fin_two.2 ⟨rfl, hσ⟩
  have hstr : z ≫ M.str = spMap (algebraMap c.F (Om Z)) := by
    show z ≫ (toFlag M ≫ flagStr TF.X) = _
    rw [← Category.assoc, hz, ptY_str]
  have hzz : spMap (ι 0) ≫ z ≠ spMap (ι 1) ≫ z := fun e => by
    letI : Algebra c.F ℂ := σ.toAlgebra
    have := eq_of_ptY_eq TF.X h Z (K := ℂ) ⟨i₁, RingHom.congr_fun (hι 0)⟩ ⟨i₂, RingHom.congr_fun (hι 1)⟩ (by
      rw [← hz, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ toFlag M) e)
    exact hne (congrArg AlgHom.toRingHom this)
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q)
  set m : ℕ := (dimFlag Dw + 2).choose 2
  have hstd : GapGe 1 std := gapGe_std Dw
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → letI := algebraΓOfHom M.str; IsNef c.F ((L₀ TF.X Z w).pull M.σ) :=
    fun w hw => TwoPoint.nef_pull hN _ M.str M.σ hV.2.1 M.proj _ (_root_.GlobalTheory.NefWt.weight_line_bundle_isNef hP hN hLie E H Dw l Xo c TF Z hF w hw)
  obtain ⟨mu, hmu0, m', hm', hA⟩ := _root_.GlobalTheory.HSApp.hodge_bundle_ample_at_regular_point hP hN hSi hCh E H Dw l Xo c TF Z hF std hstd _ hη
  have C := (common₀ TF.X Z).pull M.σ
  have e₁ := cls_common_add C (m' • std - mu) mu
  rw [sub_add_cancel] at e₁
  replace e₁ := (cls_nsmul C m' std).symm.trans e₁
  have e₂ := cls_common_add C (m • std) (la - FlagTan.kap Dw - m • std)
  rw [add_sub_cancel] at e₂
  replace e₂ := e₂.trans (congrArg (· + _) (cls_nsmul C m std))
  have hk : ∀ n, ⊤ ≤ (spMap (ι n) ≫ z) ⁻¹ᵁ (tens M.K.bundle ((L₀ TF.X Z (la - FlagTan.kap Dw)).pull M.σ)).U j :=
    fun n => (le_iff_ptOf_mem _ _).2 (by rw [ptOf_spMap_comp]; exact hj)
  have main := fun (a : Fin 2 → ℂ) (ha : ∀ n, a n ≠ 0) =>
    TwoPoint.separate_two (TwoPoint.separatesOnSmooth_of_pair hS) hN c.F σ M.X M.str (dimFlag Dw) M.proj hconn hD M.K
      _ _ _ _ _ _ _ _ _ _ m' m (nef std (hstd.mono zero_le_one)) (nef _ (gapGe_sub_std m _ hg)) (nef mu hmu0) le_rfl hm'
      e₁ e₂ (fun n => spMap (ι n) ≫ z) hzz
      (fun n => by rw [Category.assoc, hstr, spMap_comp_ring, hι])
      (fun n s => by
        have e : (spMap (ι n) ≫ z) s = ptOf z := congrArg z (Subsingleton.elim (α := PrimeSpectrum (Om Z)) _ _)
        rw [e]
        exact AmplePull.ampleAt_pull _ _ M.σ _ (isLB_L₀ TF.X Z _) _ hA)
      (fun _ => j) hk a ha
  have hvι : ∀ n g, H0.val (spMap (ι n) ≫ z) j le_top (hk n) g = ι n (T' * genVal Z (F g).1) := fun n g => by
    rw [← hval]
    exact GlobalTheory.CuspOnTor.val_spMap (ι n) z j le_top hj' le_top (hk n) g
  by_cases h0 : ∃ g₀, genVal Z (F g₀).1 ≠ 0
  · obtain ⟨g₀, hg₀⟩ := h0
    have hn : ∀ n, ι n (T' * genVal Z (F g₀).1) ≠ 0 := fun n => (map_ne_zero _).2 (mul_ne_zero hT' hg₀)
    refine main ![(i₁ (T' * genVal Z (F g₀).1))⁻¹, -(i₂ (T' * genVal Z (F g₀).1))⁻¹]
      (Fin.forall_fin_two.2 ⟨inv_ne_zero (hn 0), neg_ne_zero.2 (inv_ne_zero (hn 1))⟩) fun g => ?_
    have e := hag (genVal Z (F g).1 / genVal Z (F g₀).1) (IntermediateField.subset_adjoin _ _ ⟨F g, F g₀, rfl⟩)
    rw [← mul_div_mul_left _ _ hT', map_div₀, map_div₀] at e
    rw [Fin.sum_univ_two, hvι, hvι]
    show (i₁ _)⁻¹ * i₁ _ + -(i₂ _)⁻¹ * i₂ _ = 0
    rw [neg_mul, ← div_eq_inv_mul, ← div_eq_inv_mul, e, add_neg_cancel]
  · push_neg at h0
    refine main (fun _ => 1) (fun _ => one_ne_zero) fun g => ?_
    simp [hvι, h0]
end Geometry
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem cusp_values_separate_general_points : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (σ : Y.d.c₂.F →+* ℂ) (A B : Subalgebra Y.d.c₂.F (Om Z)), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ ratioField (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)))) ∧ IntermediateField.adjoin Y.d.c₂.F (A : Set (Om Z)) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : Y.d.c₂.F, x (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : Y.d.c₂.F, y (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) → (∀ a : A, (a : Om Z) ∈ B → y a = x a) → y = x) := by
  intro hX hG hQ hSi hP _ _ D T _ j hp hq Y e o hY u hu Z
  have hf : 2 < Module.finrank ℚ D.host.E / 2 := by
    have := D.eight_le_f
    rw [D.host.finrank_E']
    omega
  have hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j) := Nat.mul_pos (by omega) (Nat.choose_pos (by omega))
  obtain ⟨TF⟩ := _root_.GlobalTheory.CompHS.TorFlagEx.nonempty_torFlag_alt hP _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have htop := _root_.GlobalTheory.SepCusp.cuspRatioField_eq_top_of_toroidalCompactification hP hG hQ.nef hSi hX.ks.toroidalChartsForFan hX.lie hX.sep TF Z Y.U hY.geo hD (by omega) u (gapGe_sub_kap u hu)
    (GlobalTheory.HSApp.vanBd_le_space D T.toCore j Y e o hY hf Z TF u)
  have := Y.d.c₂.fin
  have : Countable Y.d.c₂.F := (Module.finBasis ℚ Y.d.c₂.F).equivFun.injective.countable
  exact exists_fg_complexPoint _ _ ((FlagDim.fnFG_fnTrdeg _ _ _ _ Y.d.Xo₂ Y.d.c₂).1 Z) _ htop
end GlobalTheory.SepCusp
end
end

section
open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cusp_values_separate_generic_points : GlobalTheory.CovTop.HypothesesX → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.SiegelToroidalIntegral → _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)), (∀ τ (a b : Fin ((T.Q.Dw j).p + (T.Q.Dw j).q)), (b : ℕ) = a + 1 → (((dimFlag (T.Q.Dw j) + 3) ^ 2 + 2 * ((T.Q.Dw j).p + (T.Q.Dw j).q) : ℕ) : ℤ) ≤ u τ a - u τ b) → ∀ Z : Comp Y.d.Xo₂ Y.d.c₂, ∃ (σ : Y.d.c₂.F →+* ℂ) (A B : Subalgebra Y.d.c₂.F (Om Z)), A.FG ∧ B.FG ∧ B ≤ A ∧ (∀ b ∈ B, b ∈ ratioField (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)))) ∧ IntermediateField.adjoin Y.d.c₂.F (A : Set (Om Z)) = ⊤ ∧ (∀ b ∈ B, b ≠ 0 → ∃ x : A →+* ℂ, (∀ k : Y.d.c₂.F, x (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) ∧ (∀ hb : b ∈ A, x ⟨b, hb⟩ ≠ 0) ∧ ∀ y : A →+* ℂ, (∀ k : Y.d.c₂.F, y (@algebraMap Y.d.c₂.F A _ _ A.algebra k) = σ k) → (∀ a : A, (a : Om Z) ∈ B → y a = x a) → y = x) := by
  first | exact @_root_.GlobalTheory.SepCusp.cusp_values_separate_general_points | exact _root_.GlobalTheory.SepCusp.cusp_values_separate_general_points | (intros; apply _root_.GlobalTheory.SepCusp.cusp_values_separate_general_points <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe
section
section
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
namespace GlobalTheory.HSApp
theorem exists_canonical_section_ne_zero_at : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.NefNumerics → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ (hV : IsVariety₀ TF.X Z) (la : AllWt.Weight Dw), GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → letI := hV.1; ∀ y ∈ U₀ TF.X Z, ∃ g : H0 (str₀ TF.X Z) (tens (CanonLB.all (str₀ TF.X Z) (dimFlag Dw)).bundle (L₀ TF.X Z (la - FlagTan.kap Dw))) ⊤, y ∈ nonzeroLocus (toSec g) := by
  intro hP hN hNa hS hT hL E _ _ _ H Dw l Xo c TF Z hF hD hV la hg
  letI := hV.1
  intro y hy
  set std : AllWt.Weight Dw := GlobalTheory.CompHt.stdWt (Psi H) (Dw.p + Dw.q) with hstd_def
  set m : ℕ := (dimFlag Dw + 1).choose 2 + 1 with hm_def
  have hstd : GapGe 1 std := gapGe_stdWt Dw
  have hmu : GapGe 0 (la - FlagTan.kap Dw - m • std) := gapGe_sub_smul m _ hg
  letI := algebraΓOfHom (str₀ TF.X Z)
  have nef : ∀ w : AllWt.Weight Dw, GapGe 0 w → IsNef c.F (L₀ TF.X Z w) :=
    fun w hw => _root_.GlobalTheory.T.base_weight_line_bundle_is_nef hP hN hL E H Dw l Xo c TF Z hF w hw
  obtain ⟨mu, hmu0, m', hm', hA⟩ := _root_.GlobalTheory.T.hodge_bundle_ample_on_regular_locus hP hN hS hT E H Dw l Xo c TF Z hF std hstd y hy
  have C := common₀ TF.X Z
  have e₁ : m' • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) =
      cls (L₀ TF.X Z (m' • std - mu)) (isLB_L₀ TF.X Z _) + cls (L₀ TF.X Z mu) (isLB_L₀ TF.X Z mu) := by
    have h := cls_common_add (common₀ TF.X Z) (m' • std - mu) mu
    rw [sub_add_cancel] at h
    rw [← h]
    exact (cls_common_nsmul (common₀ TF.X Z) m' std).symm
  have e₂ : cls (L₀ TF.X Z (la - FlagTan.kap Dw)) (isLB_L₀ TF.X Z _) =
      m • cls (L₀ TF.X Z std) (isLB_L₀ TF.X Z std) + cls (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (isLB_L₀ TF.X Z _) := by
    have h := cls_common_add (common₀ TF.X Z) (m • std) (la - FlagTan.kap Dw - m • std)
    rw [add_sub_cancel] at h
    rw [h]
    exact congrArg (· + _) (cls_common_nsmul (common₀ TF.X Z) m std)
  obtain ⟨s, hs⟩ := GlobalTheory.T.effective_generation_canonical_nef_numberField hNa hN c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) hV.2.1 hV.2.2 hD
    (CanonLB.all _ _) (L₀ TF.X Z std) (L₀ TF.X Z (la - FlagTan.kap Dw - m • std)) (L₀ TF.X Z (la - FlagTan.kap Dw))
    (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) (isLB_L₀ TF.X Z _) m' m y (nef std (hstd.mono (by norm_num))) (nef _ hmu)
    (by omega) ⟨_, _, isLB_L₀ TF.X Z (m' • std - mu), isLB_L₀ TF.X Z mu, hm', e₁, hA, nef mu hmu0⟩ e₂
  refine ⟨H0.ofSec _ ⊤ s, ?_⟩
  rwa [show toSec (H0.ofSec (str₀ TF.X Z) ⊤ s) = s from H0.bijective_ofSec_top.1 (ofSec_toSec _)]
theorem globally_generated_on_open_of_weight_gap_ge : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  intro hP hG hQ hNa hPr hS hT hL E _ _ _ H Dw l Xo c TF Z r U hF hD la hg hC
  have hV := @GlobalTheory.VarFlag.isVariety₀_flag E _ _ _ H Dw l Xo c TF Z hF
  have hpq : 1 ≤ Dw.p + Dw.q := by
    by_contra h
    have h0 : Dw.p + Dw.q = 0 := by omega
    have : dimFlag Dw = 0 := by
      unfold GlobalTheory.FlagTan.dimFlag
      rw [h0]
      simp
    omega
  let M : Modif (str₀ TF.X Z) (U₀ TF.X Z) (dimFlag Dw) := Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)
  obtain ⟨ω⟩ := GlobalTheory.CompHS.canId_nonempty hP.p5 E H Dw l Xo c TF.Y TF.X Z M (fun K _ _ y => _root_.GlobalTheory.T.flag_tangent_kodaira_spencer_iso hP hG E H Dw l Xo c K y hpq)
  intro y hy
  rw [mem_support_baseIdeal]
  push_neg
  obtain ⟨g, hgy⟩ := _root_.GlobalTheory.HSApp.exists_canonical_section_ne_zero_at hP hQ.nef hNa hS hT hL E H Dw l Xo c TF Z hF hD hV la hg y hy
  haveI := hV.1
  haveI : SmoothOfRelativeDimension (dimFlag Dw) (𝟙 (Y₀ TF.X Z) ≫ str₀ TF.X Z) := M.smooth
  obtain ⟨g', hg'⟩ := GlobalTheory.ModifRefl.exists_sec_canon_tens_pull_id c.F (Y₀ TF.X Z) (str₀ TF.X Z) (dimFlag Dw) _ (isLB_L₀ TF.X Z _) g y hgy
  have hyM : (y : M.X) ∈ M.off := by
    rw [M.off_eq]
    exact hy
  obtain ⟨s, hs, hsy⟩ := _root_.GlobalTheory.T.exists_form_nonvanishing_at_cusp hP hG E H Dw l Xo c TF Z hF M ω la g' y hyM hg'
  exact ⟨s, hC.2 hs, hsy⟩
end GlobalTheory.HSApp
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.HSCore.Quoted → GlobalTheory.Published.NadelVanishingAndNonKltDivisor → GlobalTheory.Published.Principalisation → GlobalTheory.Published.SiegelToroidalIntegral → GlobalTheory.Published.ToroidalChartsForFan → GlobalTheory.Published.SemiAbelianLieSeminegative → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), FnAlgClosed (Xo := Xo) (c := c) → 1 ≤ dimFlag Dw → ∀ la : AllWt.Weight Dw, GapGe (((dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap Dw) → CuspIso TF.X Z U la → FreeOnOpen TF.X Z U la := by
  first | exact @_root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge | exact _root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge | (intros; apply _root_.GlobalTheory.HSApp.globally_generated_on_open_of_weight_gap_ge <;> assumption)
end
end

