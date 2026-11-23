module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0212
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0008
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0075
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsThetaBasisOfFactor
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0204
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0137
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0201
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.PFibreMahlerForms
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0132
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0211
public import Development.WeilBound.CoreStatements.SesquilinearFractions.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0173
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0052
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0043
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0213
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0168
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.RiemannLatticeIsometryTransport
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCRing
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0115
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ArchimedeanFrameOfPullback
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FrameLen

theorem len_sq_eq_pi_herm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ D.t.G.left) (g : ℕ) (u : HolUnif A (D.t.PP.L.pull φ) g) (Hm : Matrix (Fin g) (Fin g) ℂ) (χ : u.Λ → ℂ), IsAbelianScheme A → IsGrpPullback A D.t.G (emb σ) φ → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) → (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) → u.IsAH Hm χ → ∀ (a : D.Frame σ) (x : D.B.carrier) (c : Fin D.g → ℂ), D.IsVec a x c → D.len σ x ^ 2 = Real.pi * (a.herm c c).re := by
  intro E _ _ _ H L _ _ D σ A _ φ g u Hm χ hab hp h1 h2 hah a x c hvec
  obtain ⟨v, hlift, v', hv', hdiff⟩ := hvec
  have e : spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L)) = emb σ := Category.comp_id _
  let v₀ : epsAt (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) ⟶ D.t.G :=
    Over.homMk v.left (by simpa using Over.w v)
  have hl₀ : (v₀.left ≫ (𝟙 D.t.G.left) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (σ.comp (algebraMap (𝓞 L) L))) ≫ (D.MB.pt x).left) := hlift
  obtain ⟨hL, hvt, -, A', _, φ', g', u', Hm', χ', p, q, a', b', hp', hah', ep, eq', dp, dq, hval⟩ :=
    D.fib σ x x v₀ v₀ hl₀ hl₀
  have hp₀ : IsGrpPullback A D.t.G (spMap (σ.comp (algebraMap (𝓞 L) L)) ≫ 𝟙 (Sp (𝓞 L))) φ :=
    IsGrpPullback.congr hp e.symm rfl
  have hpz : IsGrpPullback A' D.t.G (emb σ) φ' := IsGrpPullback.congr hp' e rfl
  let x₁ : epsR ℂ ⟶ A := (HodgeLin.tanEquiv hp₀).symm v₀
  have hx₁ : HodgeLin.tanEquiv hp₀ x₁ = v₀ := (HodgeLin.tanEquiv hp₀).apply_symm_apply _
  have tx₁ : IsTangent x₁ := (HodgeLin.isTangent_iff hp₀ x₁).2 (by rw [hx₁]; exact hvt)
  have lx₁ : x₁.left ≫ φ = v.left := congrArg (fun r => r.left) hx₁
  obtain ⟨w, hw, -⟩ := h1 x₁ tx₁
  have T1 := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) A a.A φ a.φ g D.g u a.u Hm a.Hm χ a.χ D.t.PP.isLB hab hp
    a.cart h1 h2 hah a.ah x₁ x₁ v' v' w w c c tx₁ tx₁ (hv'.trans lx₁.symm) (hv'.trans lx₁.symm) hw hw hdiff hdiff
  have T2 := _root_.GlobalTheory.CompanionTheory.Ar.HodgeUniq.hermForm_eq_of_pullbacks (Sp (𝓞 L)) D.t.G D.t.PP.L (emb σ) A A' φ φ' g g' u u' Hm Hm' χ χ' D.t.PP.isLB hab hp
    hpz h1 h2 hah hah' x₁ x₁ q p w w b' a' tx₁ tx₁ (eq'.trans lx₁.symm) (ep.trans lx₁.symm) hw hw dq dp
  have hH : a.herm c c = hermForm Hm' b' a' := T1.trans T2.symm
  have hin : ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ) =
      Real.pi * a.herm c c := by
    rw [hH]; exact hval
  have hnn : 0 ≤ ((D.B.metric.form σ).inner ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x)
      ((1 : ComplexAt σ) ⊗ₜ[𝓞 L] x) : ℂ).re := (D.B.metric.form σ).re_inner_nonneg _
  unfold PPData.len
  rw [Real.sq_sqrt hnn, hin, Complex.re_ofReal_mul]

end GlobalTheory.CompanionTheory.Ar.Sl.FrameLen
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPackPureFrameOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.Fl.CMValue

theorem det_rows (p q : ℕ) (z₁ z₂ : ℂ) (G : Matrix (Fin q) (Fin q) ℂ) (hz : z₂ ≠ 0) (hG : G.det ≠ 0) :
    (Matrix.fromRows (Matrix.fromCols (z₁ • (1 : Matrix (Fin p) (Fin p) ℂ)) (0 : Matrix (Fin p) (Fin q) ℂ))
      (Matrix.fromCols (0 : Matrix (Fin q) (Fin p) ℂ) (z₂⁻¹ • G⁻¹))).det * (z₂ ^ q * G.det) = z₁ ^ p := by
  rw [Matrix.fromRows_fromCols_eq_fromBlocks, Matrix.det_fromBlocks_zero₂₁, Matrix.det_smul, Matrix.det_one,
    Matrix.det_smul, Matrix.det_nonsing_inv]
  simp only [Fintype.card_fin, mul_one, Ring.inverse_eq_inv', inv_pow]
  field_simp

theorem range_comp {K L : Type} [Field K] [Field L] (f : K →+* L) {Y : Scheme.{0}} (y : Sp K ⟶ Y) :
    Set.range (spMap f ≫ y) = Set.range y := by
  ext t
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨spMap f s, by simp⟩
  · rintro ⟨s, rfl⟩
    obtain ⟨s'⟩ : Nonempty (Sp L) := inferInstance
    refine ⟨s', ?_⟩
    have : spMap f s' = s := Subsingleton.elim (α := PrimeSpectrum K) _ _
    simp [this]

theorem tyPart_smul {E : Type} [Field E] {g : ℕ} (ty : Fin g → (E →+* ℂ)) (τ : E →+* ℂ) (a : ℂ) (z : Fin g → ℂ) :
    tyPart ty τ (a • z) = a • tyPart ty τ z := by
  ext k
  simp only [tyPart, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> simp

end GlobalTheory.CompanionTheory.Ar.Fl.CMValue

namespace GlobalTheory.CompanionTheory.Ar.Fl.CMValue

theorem conj_cmHostRoot_ne_self {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    starRingEnd ℂ H.rt0 ≠ H.rt0 := by
  intro h
  obtain ⟨r, hr⟩ := Complex.conj_eq_iff_real.1 h
  have h1 := H.sqrt_neg_disc_sq
  rw [hr] at h1
  have h2 : r ^ 2 = -(H.d : ℝ) := by exact_mod_cast h1
  have h3 : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  nlinarith [sq_nonneg r]

end GlobalTheory.CompanionTheory.Ar.Fl.CMValue

theorem GlobalTheory.CompanionTheory.Ar.Fl.CMValue.value_on_cmFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (x : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (hx : IsPure hP x) (U : Set (Xo.XF c)) (τ : E →+* ℂ) (φ : FrameFn Xo c) (e : Fin D.p ⊕ Fin D.q → (FU.Di i).La) (ρ : ℂ) (T : Matrix (Fin D.p ⊕ Fin D.q) (Fin D.p ⊕ Fin D.q) E) (v : Vecs X.y D.p) (w : Vecs X.y D.q), IsTypeFn H D.p D.q ty → τ (H.rt : E) = H.rt0 → (∀ P (y : Sp ℂ ⟶ Xo.XF c), IsPeriod (FU.Di i) ty P → under y = FU.u i P → y ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) → Set.range y ⊆ U) → IsLineFn U τ φ → LinearIndependent (𝓞 E) e → IsConstMul U τ φ FU i e ρ → LinearIndependent (𝓞 E) x → IsTransition (FU.Di i) x e T → X.IsCMFrame τ hx v w → IsFramed U τ X.β X.y v w ∧ ((φ X.K X.y v w : X.K) : ℂ) * τ T.det * (Z true).z ^ D.p = ρ * (Z false).z ^ D.q * τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X x hx U τ φ e ρ T v w hty hτ hmem hline he hconst hxi hT hfr
  have hfr0 := (_root_.GlobalTheory.CompanionTheory.Relay.cm_pack_pure_frame E H D l Xo c g ty FU i Z P hP X x hx τ hty hτ hxi).2 v w hfr
  let f : X.K →+* ℂ := algebraMap X.K ℂ
  have hcomp : f.comp X.β = algebraMap c.F ℂ := by ext a; rfl
  let y' : Sp ℂ ⟶ Xo.XF c := spMap f ≫ X.y
  have hyu : under y' = spMap f ≫ under X.y := Category.assoc _ _ _
  have hy'u : under y' = FU.u i P := hyu.trans X.pt
  have hy's : y' ≫ pullback.snd _ _ = spMap (algebraMap c.F ℂ) := by
    rw [Category.assoc, X.hy, ← hcomp, spMap_comp]
  have hU : Set.range X.y ⊆ U := by
    rw [← CMValue.range_comp f X.y]
    exact hmem P y' hP hy'u hy's
  have hF : IsFramed U τ X.β X.y v w := ⟨hfr0.1, hU, hfr0.2.2⟩
  obtain ⟨⟨v', hv'⟩, hv⟩ := _root_.PositivityTheory.Xgf.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y')
    (X.β.comp (tauIn c τ)) D.p v hyu
  obtain ⟨⟨w', hw'⟩, hw⟩ := _root_.PositivityTheory.Xgf.tangent_vectors_base_change E H Xo.X Xo.univ.t X.K ℂ f (under X.y) (under y')
    (X.β.comp (tauIn c (ComplexEmbedding.conjugate τ))) D.q w hyu
  have hF' : IsFramed U τ (algebraMap c.F ℂ) y' v' w' := by
    refine ⟨hy's, ?_, ?_, ?_⟩
    · rw [CMValue.range_comp f X.y]; exact hU
    · have := (hv v' hv').1 hF.2.2.1
      rwa [← RingHom.comp_assoc, hcomp] at this
    · have := (hw w' hw').1 hF.2.2.2
      rwa [← RingHom.comp_assoc, hcomp] at this
  have hz₂ : (Z false).z ≠ 0 := _root_.GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero E H _ (Z false)
  have hcard : Fintype.card (Fin D.p ⊕ Fin D.q) = (FU.Di i).p + (FU.Di i).q := by
    simp [(FU.sig i).1, (FU.sig i).2]

  have hTdet : T.det ≠ 0 := by
    obtain ⟨T', hT', -, hT'det, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.transition_matrix_exists E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x e hcard he
    have hge := (_root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) e hcard he).1
    have hmul : T * gramE (FU.Di i) e = T' * gramE (FU.Di i) e := by
      ext m n
      simp only [Matrix.mul_apply, gramE, Matrix.of_apply]
      rw [← hT m (e n), ← hT' m (e n)]
    have hTT : T = T' := by
      have hu : IsUnit (gramE (FU.Di i) e).det := isUnit_iff_ne_zero.2 hge
      rw [← Matrix.mul_nonsing_inv_cancel_right _ T hu, hmul, Matrix.mul_nonsing_inv_cancel_right _ T' hu]
    rw [hTT]
    exact hT'det hxi
  have hconst' := _root_.GlobalTheory.CompanionTheory.Ar.Fl.constMul_change_generator E H D l Xo c g ty FU i U τ φ e x T ρ he hT hTdet hconst

  have orth : ∀ a j, sesq (FU.Di i) (x (.inl a)) (x (.inr j)) = 0 ∧ sesq (FU.Di i) (x (.inr j)) (x (.inl a)) = 0 :=
    fun a j => _root_.GlobalTheory.CompanionTheory.Ar.PureOrth.sesq_eq_zero_of_opposite_pure E H (FU.Di i) g ty P hP _ _ (hx.1 a) (hx.2 j)
  have hgram : gramE (FU.Di i) x =
      Matrix.fromBlocks (gramE (FU.Di i) (x ∘ Sum.inl)) 0 0 (gramE (FU.Di i) (x ∘ Sum.inr)) := by
    ext m n
    rcases m with a | j <;> rcases n with b | k
    · rfl
    · exact (orth a k).1
    · exact (orth b j).2
    · rfl
  have hG₀ : (gramE (FU.Di i) (x ∘ Sum.inr)).det ≠ 0 := by
    have h := (_root_.GlobalTheory.CompanionTheory.Relay.gram_det_ne_zero_local_basis_cofinite E H (FU.Di i) (Fin D.p ⊕ Fin D.q) x hcard hxi).1
    rw [hgram, Matrix.det_fromBlocks_zero₂₁] at h
    exact right_ne_zero_of_mul h
  let G : Matrix (Fin D.q) (Fin D.q) ℂ := τ.mapMatrix (gramE (FU.Di i) (x ∘ Sum.inr))
  have hGdet : G.det = τ (gramE (FU.Di i) (x ∘ Sum.inr)).det := (RingHom.map_det τ _).symm
  have hG : G.det ≠ 0 := by
    rw [hGdet]
    exact (map_ne_zero τ).2 hG₀
  have hGu : IsUnit G.det := isUnit_iff_ne_zero.2 hG

  have hDV : ∀ a, IsDerivAt0 (fun z => (FU.ex i P z).left)
      ((Z true).z • tyPart ty τ (P (x (.inl a)))) (v' a).left := by
    intro a
    rw [hv' a]
    exact GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X true τ ⟨x (.inl a), hx.1 a⟩ (v a) (hfr.1 a)
  have hDW : ∀ j, IsDerivAt0 (fun z => (FU.ex i P z).left)
      ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) (w' j).left := by
    intro j
    rw [hw' j]
    exact GlobalTheory.T.cm_pack_eigen_period E H D l Xo c g ty FU i Z P hP X false (ComplexEmbedding.conjugate τ)
      ⟨x (.inr j), hx.2 j⟩ (w j) (hfr.2 j)
  have hvan : ∀ a, tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inl a))) = 0 := by
    intro a
    ext k
    by_cases hk : ty k = ComplexEmbedding.conjugate τ
    · have : P (x (.inl a)) k = 0 := by
        apply hx.1 a k
        rw [hk, ComplexEmbedding.conjugate_coe_eq, hτ]
        simpa [sgnRt] using CMValue.conj_cmHostRoot_ne_self H
      simp [tyPart, this]
    · simp [tyPart, hk]
  have hC : ∀ a, tyPart ty τ (∑ m, Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ))
      (0 : Matrix (Fin D.p) (Fin D.q) ℂ) a m • P (x m)) = (Z true).z • tyPart ty τ (P (x (.inl a))) := by
    intro a
    rw [← CMValue.tyPart_smul]
    congr 1
    simp [Fintype.sum_sum_type, Matrix.one_apply, ite_smul]
  have hB : ∀ n, tyPart ty (ComplexEmbedding.conjugate τ) (P (x n)) =
      ∑ j, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n •
        ((Z false).z • tyPart ty (ComplexEmbedding.conjugate τ) (P (x (.inr j)))) := by
    intro n
    rcases n with a | k
    · simp [hvan a]
    · simp [Matrix.one_apply, ite_smul, smul_smul, hz₂]
  have hFm : ∀ j n, ∑ m, Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹) j m *
      τ (sesq (FU.Di i) (x m) (x n)) =
      Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ)) j n := by
    intro j n
    rw [Fintype.sum_sum_type]
    rcases n with a | k
    · simp [(orth a _).2]
    · have h : ((Z false).z⁻¹ • G⁻¹) * G = (Z false).z⁻¹ • (1 : Matrix (Fin D.q) (Fin D.q) ℂ) := by
        rw [Matrix.smul_mul, Matrix.nonsing_inv_mul _ hGu]
      have h' := congrFun (congrFun h j) k
      rw [Matrix.mul_apply] at h'
      simpa [G, gramE, RingHom.mapMatrix_apply] using h'
  have key := hconst' P y' v' w' _ _ _ _ _ hP hy'u hF' hDV hDW hC hB hFm
  have hnat : φ ℂ y' v' w' = f (φ X.K X.y v w) := hline.nat X.K ℂ f X.β X.y v w y' v' w' hF rfl hv' hw'
  have hrows := CMValue.det_rows D.p D.q (Z true).z (Z false).z G hz₂ hG
  refine ⟨hF, ?_⟩
  have hτT : τ T.det ≠ 0 := (map_ne_zero τ).2 hTdet
  rw [hnat] at key
  change f (φ X.K X.y v w) * τ T.det * (Z true).z ^ D.p = _
  rw [← hrows, ← hGdet]
  have key' : f (φ X.K X.y v w) * (Matrix.fromRows (Matrix.fromCols ((Z true).z • (1 : Matrix (Fin D.p) (Fin D.p) ℂ))
      (0 : Matrix (Fin D.p) (Fin D.q) ℂ)) (Matrix.fromCols (0 : Matrix (Fin D.q) (Fin D.p) ℂ) ((Z false).z⁻¹ • G⁻¹))).det * τ T.det = ρ := by
    rw [key]
    field_simp
  rw [← key']
  ring
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexAbelianFibreAmple
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.FibrePol

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open _root_.GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

theorem exists_fibre_pol : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (σ : L →+* ℂ), ∃ (t' : SAB H (Sp ℂ)) (_ : SABMap t' D.t (emb σ)), IsProper t'.G.hom ∧ Out.RelAmple t'.G t'.PP.L := by
  intro E _ _ _ H L _ _ D σ
  have hC := Out.CubePf.cubePull
  let m₁ := PullbackSections.sabM hC (spMap σ) D.tK
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ D.m m₁
  have e : spMap σ ≫ spMap (algebraMap (𝓞 L) L) = emb σ := by
    simp only [emb, spMap, ← Spec.map_comp]
    rfl
  obtain ⟨w, hw, -⟩ := m₁.lin
  refine ⟨PullbackSections.sabT hC (spMap σ) D.tK, e ▸ n, ?_, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @IsProper) m₁.cart.1 D.princ.1
  · exact relAmple_pull m₁.cart.1 D.tK.PP.isLB (PullbackSections.sabT hC (spMap σ) D.tK).PP.isLB ((isGen_iff w).1 hw) ⊤
      (isAffineOpen_top _) (fun _ => trivial) D.princ.2.1

end GlobalTheory.CompanionTheory.Ar.Sl.FibrePol
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CuspVolumeMiddle
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp MeasureTheory

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

theorem coordsAt_torusSmul {X : Scheme.{0}} {Ω : Type} [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) {K : Type} [Fintype K]
    {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {z : Spec (CommRingCat.of ℂ) ⟶ X} {w : (Σ k, J k) → ℂ}
    (h : CoordsAt ξ y z w) {a : K → ℂ} (ha : ∀ k, a k ≠ 0) : CoordsAt ξ y z (torusSmul a w) := by
  have hs : ∀ q : Σ k, J k, torusSmul a w q = a q.1 * w q := fun q => rfl
  refine ⟨fun k => ?_, fun k c hc => ?_⟩
  · obtain ⟨c, hc⟩ := h.1 k
    refine ⟨c, ?_⟩
    rw [hs]
    exact (isUnit_iff_ne_zero.2 (ha k)).mul hc
  · have hc' : IsUnit (w ⟨k, c⟩) := by
      rw [hs] at hc
      exact isUnit_of_mul_isUnit_right hc
    obtain ⟨hy, hv⟩ := h.2 k c hc'
    refine ⟨hy, fun i => ?_⟩
    obtain ⟨r, hr, he⟩ := hv i
    refine ⟨r, hr, ?_⟩
    rw [hs, hs]
    show a k * w ⟨k, i⟩ = r * (a k * w ⟨k, c⟩)
    rw [he]
    ring

theorem valAt_eq {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hξ : IsCptGen ξ)
    {R : Type} [CommRing R] [IsLocalRing R] {z : Spec (CommRingCat.of R) ⟶ X} (h : genPt ξ ⤳ centre z) {a : Ω} {r r' : R}
    (h₁ : ValAt ξ z a r) (h₂ : ValAt ξ z a r') : r = r' := by
  obtain ⟨φ, hφ, -⟩ := ValHom.exists_valAt_hom X Ω ξ R z h hξ
  obtain ⟨_, e₁⟩ := (hφ a r).1 h₁
  obtain ⟨_, e₂⟩ := (hφ a r').1 h₂
  exact e₁.symm.trans e₂

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {Xo : ∀ l : Tor.Level H, Moduli D l}
  {l : Tor.Level H} {c : Coeff l} {Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)} {II : IntersectionSystem} {K : Type}
  [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω : Type} [Field Ω] [Algebra ℚ Ω] {W : CMType H → Type}
  [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] {Dc : ComponentData II (CMType H) K J Ω W} {Hd : HodgeData Dc}
  {S₀ : Finset ℕ}

theorem isCMFam_of_labVal (Or : CptOrigin Y S₀ Dc Hd) {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X}
    {σ : CMType H → (𝓞 E →+* ℂ)} (hL : Or.𝔐.LabVal z Or.sm σ) : IsCMFam σ := by
  obtain ⟨σ₀, h0, -, -, -, -, hcm⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.LabPt.exists_labVal E H D l (Xo l) c Y S₀ Ω K J Dc.y Or.𝔐 ℂ z
  have hs : ∀ τ, σ τ = σ₀ (Or.sm τ) := fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL τ a) (h0 (Or.sm τ) a)
  obtain ⟨h1, h2, -⟩ := hcm (RingHom.id ℂ)
  have he : σ = fun τ => σ₀ (Or.sm τ) := funext hs
  rcases Or.side with ⟨-, h, -⟩ | ⟨-, h, -⟩
  · rw [he, h]
    exact h2
  · rw [he, h]
    exact h1

theorem eq_cuspW_of_fibre (Or : CptOrigin Y S₀ Dc Hd) {U : ((Σ k, J k) → ℂ) → ℝ} (hU : Or.𝔐.IsCuspWeight Or.sm U)
    {z : Spec (CommRingCat.of ℂ) ⟶ Or.𝔐.X} {w : (Σ k, J k) → ℂ} (hw : CoordsAt Or.𝔐.ξ Dc.y z w) (hz : Or.𝔐.Interior z)
    {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) {σ : CMType H → (𝓞 E →+* ℂ)}
    (hF : FibreLat Or.𝔐.t z R) (hL : Or.𝔐.LabVal z Or.sm σ) : U w = R.cuspW σ := by
  obtain ⟨g', Λ', i₁, i₂, R', σ', hF', hL', he⟩ := hU z w hw hz
  have hσ : σ' = σ := funext fun τ => RingHom.ext fun a =>
    valAt_eq Or.𝔐.tie.gen (Or.𝔐.all _) (hL' τ a) (hL τ a)
  subst hσ
  obtain ⟨φ, h1, h2, h3, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Cusp.FibreUnique.exists_linearEquiv_of_fibreLatVec E H Or.𝔐.X Or.𝔐.t z g' g Λ' Λ R' R Empty _ _ _ hF' hF
  rw [he]
  exact (_root_.LevelTowerAlt.riemann_lattice_isometry_transport E g' Λ' (CMType H) R' σ' g Λ R φ (isCMFam_of_labVal Or hL) h1 h2 h3).1.symm

theorem cuspWeight_torus_and_sheets : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (II : IntersectionSystem) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : CMType H → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (Dc : ComponentData II (CMType H) K J Ω W) (Hd : HodgeData Dc) (S₀ : Finset ℕ) (Or : CptOrigin Y S₀ Dc Hd) (Q : Pieces Or) (U : ((Σ k, J k) → ℂ) → ℝ), Or.𝔐.IsCuspWeight Or.sm U → (∀ w ∈ Dc.Xo, ∀ w' ∈ torusSat {w}, U w' = U w) ∧ ∀ m, ∀ t ∈ Q.V m, U (Q.γ m t) = ((Q.F (Q.pc m)).R t).cuspW (Q.F (Q.pc m)).σ := by
  intro E _ _ _ _ H D Xo l c Y II K _ J _ Ω _ _ W _ _ Dc Hd S₀ Or Q U hU
  refine ⟨fun w hw w' hw' => ?_, fun m t ht => ?_⟩
  · obtain ⟨z, -, hz⟩ := (_root_.GlobalTheory.CompanionTheory.Ar.mem_mcPts_iff_exists_coordsAt Or.𝔐.X Ω Or.𝔐.ξ K J Dc.y Or.𝔐.tie w).1 hw.1
    have hI : Or.𝔐.Interior z := by
      by_contra hn
      exact hw.2 ((Or.bd z w hz).2 hn)
    obtain ⟨u, hu, a, ha, rfl⟩ := hw'
    rw [show u = w from hu]
    obtain ⟨g, Λ, i₁, i₂, R, σ, hF, hL, he⟩ := hU z w hz hI
    rw [he]
    exact eq_cuspW_of_fibre Or hU (coordsAt_torusSmul Or.𝔐.ξ hz ha) hI R hF hL
  · obtain ⟨z, hz, hI, hF, hL⟩ := Q.fibre m t ht
    exact eq_cuspW_of_fibre Or hU hz hI _ hF hL

end GlobalTheory.CompanionTheory.Ar.Cusp.WeightSheet

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbelianPartExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar

theorem abPart_exists (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S)
    (L : Type) [Field L] [NumberField L] (z : Sp L ⟶ S) :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (e : L →+* L'), Nonempty (AbPart t (spMap e ≫ z)) := by
  obtain ⟨L', _, _, hfin, ⟨τ⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.exists_finite_torusExtension_fibre S t.G t.semi L z
  have : CharZero L' := charZero_of_injective_algebraMap (algebraMap L L').injective
  have : NumberField L' := NumberField.of_module_finite L L'
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.proved_CubePullSt (spMap (algebraMap L L') ≫ z) t
  obtain ⟨tB, e, he, ha, hp⟩ := GlobalTheory.T.torus_extension_abelian_quotient E H L'
    ⟨(Over.pullback (spMap (algebraMap L L') ≫ z)).obj t.G, IsSemiAbelian.pullback _ t.G t.semi,
      OAct.pullback _ t.G t.act, PP', cub, sym, adj, prim⟩ τ
  exact ⟨L', _, inferInstance, algebraMap L L', ⟨⟨_, m, τ, tB, e, he, ha, hp⟩⟩⟩

end GlobalTheory.CompanionTheory.Ar
end
end

