module

public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2767
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0001
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0018
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0009
public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerCanonicalDivisor
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2774
public import Development.WeilBound.CoreStatements.NefModelVolumes.NormGenValLe
public import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.Bundle0003
public import Development.WeilBound.CoreStatements.NefModelVolumes.InjectivityWeightSectionsOf
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Bundle0012

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsPowMulMemCuspFormsOfWeightMatch
section
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace _root_.CategoryTheory.Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.WtMatchBar
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 800000 in
theorem exists_pow_mul_mem_cuspForms_of_weight_match : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  intro hP D T j Y e o hY hE hp hq la hla hbar f hf
  obtain ⟨u, u', t₁, hu, ht₁, huu, hu'⟩ := _root_.GlobalTheory.T.inverse_invariant_integral hP D T j Y e o hY hE
  obtain ⟨N, hN, hU2⟩ := _root_.GlobalTheory.T.detLine_flat_unit_exists hP D T j Y e o hY hE
  obtain ⟨M, hM⟩ : ∃ M : ℕ, M = 4 * (Module.finrank ℚ D.host.E * D.R.r) + 3 + 1 := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ := _root_.GlobalTheory.T.exists_pow_mul_unit_mem_cusp hP D T j Y e o hY hE la f hf (u ^ M) (u' ^ M) (t₁ ^ M) _ (pow_mem_secZ hu M)
    (pow_ne_zero _ ht₁) (by rw [← mul_pow, huu, smul_pow, one_pow])
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = max K (2 * M + N) := ⟨_, rfl⟩
  obtain ⟨w, a, hDom, hex⟩ := _root_.GlobalTheory.WtMatchArithBar.exists_dom_exponents_bar _ _ _ la hp hq hla hbar N M k hN (by omega)
  obtain ⟨φ, φ', t₂, hφ, ht₂, hφφ, hφ', hφb⟩ := hU2 w
  refine ⟨k, a, 2 * M, u ^ M * φ, u' ^ M * φ', t₁ ^ M * t₂, hDom, by omega, ?_, mul_ne_zero (pow_ne_zero _ ht₁) ht₂, ?_, ?_⟩
  · refine hK k (hk ▸ le_max_left _ _) φ φ' t₂ _ hφ ht₂ hφφ hφb a (2 * M) hDom ?_
    rw [← GlobalTheory.AllWt.secZ_nat, hex]
    have h1 : f ^ (k + 1) ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ ((k + 1) • GlobalTheory.AllWt.exOf (T.Q.Dw j) la 0) :=
      pow_mem_secZ (GlobalTheory.AllWt.cuspW_le_secZ _ hf) (k + 1)
    have h2 := GlobalTheory.AllWt.mul_mem_secZ h1 (GlobalTheory.AllWt.mul_mem_secZ (pow_mem_secZ hu M) hφ)
    convert h2 using 2
    rw [nsmul_exOf_zero_one, ← GlobalTheory.AllWt.exOf_add, zero_add, add_zero]
  · rw [mul_mul_mul_comm, ← mul_pow, huu, hφφ, smul_pow, one_pow, smul_mul_smul_comm, one_mul]
  · intro la' v hv
    have hV := isVal_valSet la' v hv
    rw [hV.mul]
    rw [hM]
    exact add_nonneg (val_pow_succ_nonneg hV (hu' la' v hv) _) (hφ' la' v hv)
end GlobalTheory.WtMatchBar
end
end

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace _root_.CategoryTheory.Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weight_match_pow_mul_cuspidal : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → ∀ la : GlobalTheory.AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → (∀ τ, 1 ≤ gap (la τ) ((T.Q.Dw j).p - 1)) → ∀ f ∈ Y.V (wtOf _ la 0), ∃ (k : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (g h : Rul Y.d.Xo₂ Y.d.c₂) (t : Y.d.c₂.F), Dom a n ∧ 4 * (Module.finrank ℚ D.host.E * D.R.r) + 4 ≤ n ∧ f ^ (k + 1) * g ∈ cusp Y.d.Xo₂ Y.d.c₂ Y.U a n ∧ t ≠ 0 ∧ g * h = t • 1 ∧ ∀ la', ∀ v ∈ valSet Y.d.Xo₂ Y.d.c₂ (algCls Y.d.Xo₂ Y.d.c₂) la', 0 ≤ v h := by
  first | exact @_root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | exact _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match | (intros; apply _root_.GlobalTheory.WtMatchBar.exists_pow_mul_mem_cuspForms_of_weight_match <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsSimpleLogPoleAlongBoundary
section
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogPole
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}
set_option maxHeartbeats 1600000 in
theorem exists_log_pole_along_boundary (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (TF : TorFlag Xo c) (Z : Comp Xo c) (hF : FnAlgClosed (Xo := Xo) (c := c))
    (hKS : ∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), KSIso (psiSet H) y)
    (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z)
    (V : (Y₀ TF.X Z).Opens) (hy : y ∈ V) :
    ∃ (W : (Y₀ TF.X Z).Opens) (_ : y ∈ W) (_ : W ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι)
      (k : TF.X.F.J) (δ u : Γ(Y₀ TF.X Z, W)),
      W ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ W ≤ inc₀ TF.X Z ⁻¹ᵁ TF.X.F.U k ∧ IsUnit u ∧
      (∀ z (hz : z ∈ W), IsUnit (ger z hz δ) ↔ z ∈ U₀ TF.X Z) ∧
      (∀ (W' : (Y₀ TF.X Z).Opens) (hW' : W' ≤ W) (f : Γ(Y₀ TF.X Z, W')), (∀ z (hz : z ∈ W'), z ∉ U₀ TF.X Z →
        ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) →
        ∀ z (hz : z ∈ W'), ger z (hW' hz) δ ∣ ger z hz f) ∧
      ∀ (K : Type) [Field K] (z : Sp K ⟶ Y₀ TF.X Z) (hz : ⊤ ≤ z ⁻¹ᵁ W) ho hi,
        ev z W hz δ * H0.val (B := LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle
          ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)) z
          (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k) ho hi ω₀.ω = ev z W hz u := by
  obtain ⟨i, hi⟩ := exists_chart (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isLB y
  obtain ⟨U, n, e₀, v, hyU, hv₀⟩ := GlobalTheory.T.exists_lieEigenBasis_near_boundaryFlagSpace_point E H Dw l Xo c TF Z hF y
  obtain ⟨e, W, k, L, N, hv, hyW, hWV, hc⟩ := _root_.GlobalTheory.LogPole.exists_isCell_near E H Dw l Xo c TF Z U n e₀ v hv₀ y hyU V hy
  obtain ⟨ε, b, hb⟩ := _root_.GlobalTheory.LogKSDiv.exists_logKS_symPair_basis E H Dw l Xo c TF U n e v _ hv.1 hv.2.1 hv.2.2
  obtain ⟨x, U', hU', hyU', hx, hbd⟩ := _root_.GlobalTheory.LogPole.exists_coord_logDet E H Dw l Xo c TF U b _ hyU
  have het := GlobalTheory.T.etale_bigCellCoordinates_flagSpace E H Dw l Xo c TF Z hF U n e v hv W k L N hc
  obtain ⟨s, hs, hcmp⟩ := _root_.GlobalTheory.T.kodaira_spencer_comparison_along_boundary hP E H Dw l Xo c TF
  let o : Fin Dw.dim ≃ HIx Dw (psiSet H) :=
    (Fintype.equivFinOfCardEq (FlagTan.card_HIx (FlagTan.isHalf_psiSet H))).symm
  obtain ⟨a, ha, hhor⟩ := _root_.GlobalTheory.LogPole.logDet_eq_hor E H Dw l Xo c TF s hs hcmp hKS U n e v hv ε b hb o
  obtain ⟨W', hW'a, hyW', hW'⟩ := Opens.isBasis_iff_nbhd.1 (Y₀ TF.X Z).isBasis_affineOpens
    (show y ∈ W ⊓ (toBase TF Z ⁻¹ᵁ U'.1 ⊓ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i) from ⟨hyW, hyU', hi⟩)
  have hW'W : W' ≤ W := hW'.trans inf_le_left
  have hW'U : W' ≤ toBase TF Z ⁻¹ᵁ U'.1 := hW'.trans (inf_le_right.trans inf_le_left)
  have hW'i : W' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i := hW'.trans (inf_le_right.trans inf_le_right)
  let O := (tanOrd Dw).trans (Equiv.sumCongr o.symm (Equiv.refl (VIx Dw)))
  let G : Fin Dw.dim ⊕ VIx Dw → Γ(Y₀ TF.X Z, W) :=
    Sum.elim (fun i => ((toBase TF Z).appLE U.1 W hc.2.1).hom (x i)) (cellCoord N)
  let g : Fin (FlagTan.dimFlag Dw) → Γ(Y₀ TF.X Z, W') := fun a => resG _ hW'W (G (O a))
  have hfr := _root_.GlobalTheory.TopFrameEt.isFrame_etale c.F TF.Y.X (Y₀ TF.X Z) TF.Y.s (toBase TF Z) (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str
    ((Category.assoc _ _ _).trans (Category.id_comp _).symm) Dw.dim (FlagTan.dimFlag Dw) TF.smooth (VIx Dw) O U.1 U'.1 hU'
    U.2 W W' hW'W hc.1 hW'a hc.2.1 hW'U (cellCoord N) het x hx
  have hJ : IsUnit ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g) :=
    ((Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.isUnit_jacobian_iff i hW'a hW'i g).2 hfr
  haveI := TF.smooth
  haveI : Smooth TF.Y.s := SmoothOfRelativeDimension.smooth Dw.dim TF.Y.s
  haveI : IsLocallyNoetherian TF.Y.X := LocallyOfFiniteType.isLocallyNoetherian TF.Y.s
  obtain ⟨r₁, r₂⟩ := _root_.GlobalTheory.EtaleReducedEq.reducedEq_pullback_etale TF.Y.X (Y₀ TF.X Z) (toBase TF Z) (VIx Dw) (LogKS.interior TF.Y) U U' hU' W hc.1 hc.2.1
    (cellCoord N) het _ hbd
  let ac : Γ(Y₀ TF.X Z, W') := algX (str₀ TF.X Z) W' (a : c.F)
  have hac : IsUnit ac := (Ne.isUnit (Rat.cast_ne_zero.2 ha)).map _
  refine ⟨W', hyW', hW'W.trans hWV, i, k,
    resG _ hW'W (((toBase TF Z).appLE U.1 W hc.2.1).hom (logDet (fun j => (b j).1) x)),
    ac * resG _ hW'W (diagUnit L hc.2.2.2.2.1).val * (show Γ(Y₀ TF.X Z, W') from
      (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.jacobian i hW'i g), hW'i, hW'W.trans hc.2.2.1,
    (hac.mul ((Units.isUnit _).map _)).mul hJ, fun z hz => ?_, fun W'' hW'' f hf z hz => ?_, fun K _ z hz ho hi => ?_⟩
  · rw [ger_resG]
    exact r₁ z (hW'W hz) (hW'U hz)
  · rw [ger_resG]
    exact r₂ W'' (hW''.trans hW'W) (hW''.trans hW'U) f hf z hz
  have eM : toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = inc₀ TF.X Z := Category.id_comp _
  have hzW := FlagMod.le_preimage_mono hW'W hz
  have hU₀ : ⊤ ≤ z ⁻¹ᵁ U₀ TF.X Z := fun p hp => by
    have := ho hp
    rw [Modif.off_eq] at this
    exact this
  have hk : ⊤ ≤ (z ≫ inc₀ TF.X Z) ⁻¹ᵁ TF.X.F.U k := FlagMod.le_preimage_map _ hc.2.2.1 hzW
  obtain ⟨_, hch⟩ := exists_chartFr (z ≫ inc₀ TF.X Z) hU₀
  obtain ⟨Q, hQ⟩ := hch k hk
  obtain ⟨P₀, P, t, hU, hQP, ht, hP₀, hB⟩ := _root_.GlobalTheory.LogPole.exists_cellFrames E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW hk Q hQ
  have ez : z ≫ inc₀ TF.X Z = TF.X.ptY P := FlagMod.FlagCover.eq_ptY (hQ.lies.frBor hQP)
  obtain ⟨w, hw⟩ := (hKS K P).exists_isTanFrame
  have ezM : z ≫ toFlag (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) = z ≫ inc₀ TF.X Z := by rw [eM]
  choose zw hzw hzO using fun b => exists_tanLift (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) (hw.isDef b)
    (ezM.trans ez) ho
  have hzw' : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ inc₀ TF.X Z = TF.X.ptY (w b) := fun b => by
    exact (congrArg (zw b ≫ ·) eM).symm.trans (hzw b)
  have hkM := ezM ▸ hk
  have key := ω₀.isKS K P Q t w z zw i k W' hW'i g hz (fun b => hzO b W' hz) hkM ho hi (chartFr_congr ezM.symm hkM hQ)
    hQP hw hzw
  obtain ⟨v₁, v₂⟩ := _root_.GlobalTheory.LogPole.vert_jac_det_one E H Dw l Xo c TF Z U n e v hv W k L N hc K z hzW P₀ P hU ez hP₀ hB (fun b => w (.inr b))
    (fun b => zw (.inr b)) (fun b => hzO _ W hzW) hw.2 (fun b => hzw' _)
  have eb : ∀ b, (show Sp (DualNumber K) ⟶ Y₀ TF.X Z from zw b) ≫ toBase TF Z = frX (w b) ≫ TF.Y.j := fun b => by
    rw [← Category.assoc, hzw', (TF.X.lies_ptY _).1]
  have hwU : ∀ b, ⊤ ≤ (frX (w b) ≫ TF.Y.j) ⁻¹ᵁ U.1 := fun b =>
    eb b ▸ FlagMod.le_preimage_map _ hc.2.1 (hzO b W hzW)
  have hdet : ∀ σ, ((N σ).map (ev z W hzW)).det = 1 := fun σ => by
    rw [Matrix.det_of_upperTriangular fun i j hij => by rw [Matrix.map_apply, hc.2.2.2.2.2.1 σ i j hij, map_zero]]
    simp [hc.2.2.2.2.2.2.1]
  have hh := hhor x K P₀ P hU _ hdet hP₀ hB (fun b => w (.inl b)) (fun b => hwU _) hw.1
  have eP : z ≫ toBase TF Z = frX P₀ ≫ TF.Y.j := by
    rw [← Category.assoc, ez, (TF.X.lies_ptY _).1,
      FlagMod.eq_frX P₀ ((FlagMod.frX_fst P).trans hP₀.1) (FlagMod.frX_snd P)]
  have hblock := det_block o (fun a b => (ev (zw b) W (hzO b W hzW) (G a)).snd) (fun i b => v₂ b _) v₁
  have e₁ : (Matrix.of fun a b => (TangentOrigin.evalPt (zw (tanOrd Dw b)) W' (hzO _ W' hz) (g a)).snd) =
      Matrix.of fun a b => (ev (zw (tanOrd Dw b)) W (hzO _ W hzW) (G (O a))).snd := by
    ext a b
    exact congrArg TrivSqZeroExt.snd (FlagMod.ev_res _ hW'W _ _ _)
  have e₂ : (Matrix.of fun i j => (ev (zw (.inl (o j))) W (hzO _ W hzW) (G (.inl i))).snd) =
      Matrix.of fun i j => (ev (frX (w (.inl (o j))) ≫ TF.Y.j) U.1 (hwU _) (x i)).snd := by
    ext i j
    exact congrArg TrivSqZeroExt.snd ((FlagMod.ev_appLE _ _ hc.2.1 _ (eb _ ▸ hwU _) _).trans
      (congrArg (· (x i)) (FlagMod.ev_congr (eb _) _ _ _)))
  rw [e₁, hblock, e₂, map_diagUnit (ev z W hzW) L hc.2.2.2.2.1 t ht] at key
  have hca : ev z W' hz ac = (a : K) := by
    haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
    exact map_ratCast ((ev z W' hz).comp (algX (str₀ TF.X Z) W')) a
  rw [FlagMod.ev_res _ hW'W hz hzW, FlagMod.ev_appLE _ _ hc.2.1 _ (eP ▸ hU), FlagMod.ev_congr eP _ _ hU, hh,
    map_mul, map_mul, hca, FlagMod.ev_res _ hW'W hz hzW, mul_assoc, mul_assoc]
  exact congrArg _ ((mul_comm _ _).trans key)
section Main
open ReciprocityTheory.GeometryOfNumbersTheory Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CovTop
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option maxHeartbeats 800000 in
theorem log_pole_along_boundary_is_simple : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  intro hP _ E _ _ _ H Dw l Xo c TF Z hF hKS hV ω₀ y _ V hy t ht₁ ht₂
  obtain ⟨W, hyW, hWV, i, k, δ, u, hi, hk, hu, h₁, h₂, h₃⟩ := _root_.GlobalTheory.LogPole.exists_log_pole_along_boundary hP TF Z hF hKS hV ω₀ y V hy
  haveI : IsDomain ((Y₀ TF.X Z).presheaf.stalk y) :=
    haveI := (TF.X.normal (inc₀ TF.X Z y)).1
    MulEquiv.isDomain _ (asIso ((inc₀ TF.X Z).stalkMap y)).commRingCatIsoToRingEquiv.symm.toMulEquiv
  obtain ⟨V', hyV', hV', b, hb, e⟩ := exists_unit_mul y hyW (resG _ hWV t) δ
    (by rw [ger_resG]; exact ger_ne_zero (dense_U₀ TF.X Z) t (fun z hz h => (ht₁ z hz).2 h) y _)
    (by rw [ger_resG]; exact ht₂ W hWV δ (fun z hz h hu => h ((h₁ z hz).1 hu)) y hyW)
    (h₂ W le_rfl _ (fun z hz h hu => h ((ht₁ z (hWV hz)).1 (by rwa [ger_resG] at hu))) y hyW)
  refine ⟨V', hyV', hV'.trans hWV, i, k, b * resG _ hV' u, hV'.trans hi, hV'.trans hk, fun z hz => ?_,
    fun z hz ho hc => ?_⟩
  · rw [map_mul]
    exact (hb z hz).mul ((hu.map _).map _)
  let O : (Y₀ TF.X Z).Opens := ksOpen (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) i k
  let ω : Γ(Y₀ TF.X Z, O) := ω₀.ω.loc (i, flagIdx (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)) _ k)
  have e₁ : resG _ (inf_le_left : W ⊓ O ≤ W) δ * resG _ inf_le_right ω = resG _ inf_le_left u := by
    refine FlagMod.ext_ev_field fun K _ p hp => ?_
    have a₁ := FlagMod.le_preimage_mono inf_le_left hp
    have a₂ := FlagMod.le_preimage_mono inf_le_right hp
    rw [map_mul, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₁, FlagMod.ev_res p _ hp a₂]
    exact h₃ K p a₁ (FlagMod.le_preimage_mono inf_le_left a₂) (FlagMod.le_preimage_mono inf_le_right a₂)
  have hzO : z ∈ O := ⟨ho, hc⟩
  have hm : z ∈ W ⊓ O := ⟨hV' hz, hzO⟩
  have e₂ := congrArg (ger z hm) e₁
  have e₃ := congrArg (ger z hz) e
  simp only [map_mul, ger_resG] at e₂ e₃
  change ger (Y := Y₀ TF.X Z) z _ t * ger (Y := Y₀ TF.X Z) z hzO ω = ger (Y := Y₀ TF.X Z) z hz _
  rw [map_mul, ger_resG, e₃, mul_assoc, e₂]
end Main
end GlobalTheory.LogPole
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
theorem _root_.GlobalTheory.T.exists_simple_log_pole_along_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → GlobalTheory.Published.GrothendieckDeformation → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (Z : Comp Xo c), FnAlgClosed (Xo := Xo) (c := c) → (∀ (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K), GlobalTheory.FlagTan.KSIso (GlobalTheory.FlagTan.psiSet H) y) → ∀ (hV : IsVariety₀ TF.X Z) (ω₀ : CanId (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z))) (y : Y₀ TF.X Z), y ∉ U₀ TF.X Z → ∀ (V : (Y₀ TF.X Z).Opens), y ∈ V → ∀ (t : Γ(Y₀ TF.X Z, V)), (∀ z (hz : z ∈ V), IsUnit (ger z hz t) ↔ z ∈ U₀ TF.X Z) → (∀ (W : (Y₀ TF.X Z).Opens) (hW : W ≤ V) (f : Γ(Y₀ TF.X Z, W)), (∀ z (hz : z ∈ W), z ∉ U₀ TF.X Z → ger z hz f ∈ IsLocalRing.maximalIdeal ((Y₀ TF.X Z).presheaf.stalk z)) → ∀ z (hz : z ∈ W), ger z (hW hz) t ∣ ger z hz f) → ∃ (V' : (Y₀ TF.X Z).Opens) (_ : y ∈ V') (hle : V' ≤ V) (i : (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.ι) (j : (common₀ TF.X Z).J) (u : Γ(Y₀ TF.X Z, V')), V' ≤ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle.U i ∧ V' ≤ (common₀ TF.X Z).U j ∧ (∀ z (hz : z ∈ V'), IsUnit (ger z hz u)) ∧ ∀ z (hz : z ∈ V') (ho : z ∈ (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).off) (hc : z ∈ (LB.div (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).K.bundle ((L₀ TF.X Z (FlagTan.kap Dw)).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ)).U (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j)), ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z (hle hz) t * H0.germ (p := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).str) (i, ((common₀ TF.X Z).pull (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).σ).idx (FlagTan.kap Dw) j) z ho hc ω₀.ω = ger (Y := (Modif.refl hV.1 hV.2.1 (dense_U₀ TF.X Z)).X) z hz u := by
  first | exact @_root_.GlobalTheory.LogPole.log_pole_along_boundary_is_simple | exact _root_.GlobalTheory.LogPole.log_pole_along_boundary_is_simple | (intros; apply _root_.GlobalTheory.LogPole.log_pole_along_boundary_is_simple <;> assumption)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.SmallSectionsInjective
section
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Points GlobalTheory.ChartGlue GlobalTheory.CechPic GlobalTheory.CxPts GlobalTheory.Cartier
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
theorem PositivityTheory.Xj7N.small_sections_injective : PositivityTheory.Xj7N.NV → _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (u : GlobalTheory.AllWt.Weight (T.Q.Dw j)) (X : AlgebraicGeometry.Scheme.{0}) [AlgebraicGeometry.IsIntegral X] (p : X ⟶ Sp (𝓞 Y.d.c₂.F)) (L : GlobalTheory.HermLB p) (ψ : Om Z →+* X.functionField) (s : latOn Y.U Z (wtOf (T.Q.Dw j) u 0) → L.B.Sec) (t : ℝ), GoodOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) → GlobalTheory.DegVal.BirOn Y.U Z (wtOf (T.Q.Dw j) u 0) → NoBase Y.U Z (wtOf (T.Q.Dw j) u 0) → 0 < Y.dg u Z → GlobalTheory.ImageModel.IsModelOf (normOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0)) (latOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (genPoint Z (cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0))) (dimFlag (T.Q.Dw j)) p L ψ s → ∀ i : ℕ, 1 ≤ i → (smallL Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z (wtOf (T.Q.Dw j) u 0) (8 * i) t).encard ≤ ((L.shift (fun _ => t) (fun _ => rfl)).pow (8 * i)).smallSec.encard :=
  fun hNV => _root_.PositivityTheory.Xj7N.Inj.small_sections_injective_of_self_intersection_bound (_root_.PositivityTheory.Xj7N.weil_height_comparison_of_degree_bound (_root_.PositivityTheory.Xj7N.weil_height_archimedean_contribution hNV))
end
end

