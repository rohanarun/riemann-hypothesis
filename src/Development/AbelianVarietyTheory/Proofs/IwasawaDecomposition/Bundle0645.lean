module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0604
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0640
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0926
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0629
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0631
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0589
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0635
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
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0469
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0480
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0095
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0632
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0462
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0045
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.CMTypeEmbeddings
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0624
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EigenCompatibleOfBadSet
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0630
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0639
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0309
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitsLiftSpec
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernPolyTopDensityCompHolomorphicNormSqDet
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame
open GlobalTheory.PointChern Filter Topology
open scoped Matrix

noncomputable section
namespace GlobalTheory.ChernPull

open ReciprocityTheory.L2DbarEstimates (V)
open ComplexConjugate

variable {n : ℕ} {r : Type} [Fintype r] [DecidableEq r]

theorem conn_eq_sum (H : V n → Matrix r r ℂ) (z ζ : V n) :
    conn H z ζ = ∑ c, ζ c • conn H z (coordVec c) := by
  have hζ : ζ = ∑ c, ζ c • coordVec (n := n) c := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdel H z (∑ c ∈ s, ζ c • coordVec c) = ∑ c ∈ s, ζ c • mdel H z (coordVec c) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdel_add_vec, mdel_smul_vec, ih]
  simp only [conn, hl, Matrix.transpose_sum, Matrix.transpose_smul, Matrix.mul_sum, Matrix.mul_smul]

theorem curv_eq_sum (H : V n → Matrix r r ℂ) (z ξ ζ : V n) :
    curv H z ξ ζ = ∑ d, conj (ζ d) • curv H z ξ (coordVec d) := by
  have hζ : ζ = ∑ d, ζ d • coordVec (n := n) d := by
    ext i; simp [coordVec, Pi.single_apply]
  conv_lhs => rw [hζ]
  have hl : ∀ (s : Finset (Fin n)), mdbar (fun x => conn H x ξ) z (∑ d ∈ s, ζ d • coordVec d) =
      ∑ d ∈ s, conj (ζ d) • mdbar (fun x => conn H x ξ) z (coordVec d) := by
    intro s
    induction s using Finset.induction_on with
    | empty => ext a b; simp
    | insert x s hx ih => rw [Finset.sum_insert hx, Finset.sum_insert hx, mdbar_add_vec, mdbar_smul_vec, ih]
  simp only [curv, hl, Finset.sum_neg_distrib, smul_neg]

theorem mContDiffAt_conn {H : V n → Matrix r r ℂ} {y : V n} (h2 : MContDiffAt 2 H y)
    (hu : IsUnit (H y).det) (ξ : V n) : MContDiffAt 1 (fun x => conn H x ξ) y := by
  have h1 : MContDiffAt 1 H y := h2.of_le (by norm_num)
  have hu' : IsUnit ((H y)ᵀ).det := by rwa [Matrix.det_transpose]
  exact (h1.transpose.inv hu').mul ((h2.mdel (j := 1) (by norm_num) ξ).transpose)

theorem conn_comp_eventually {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (ξ : V n) :
    ∀ᶠ w in 𝓝 v, conn (fun x => H (φ x)) w ξ = ∑ c, (fderiv ℂ φ w ξ) c • conn H (φ w) (coordVec c) := by
  have hK : ∀ᶠ w in 𝓝 v, MContDiffAt 2 H (φ w) := hφ.continuousAt.eventually h2.eventually_two
  filter_upwards [hK, hφ.eventually_analyticAt] with w hw ha
  rw [← conn_eq_sum]
  have hm : mdel (fun x => H (φ x)) w ξ = mdel H (φ w) (fderiv ℂ φ w ξ) := by
    ext a b
    exact del_comp_holo (u := fun y => H y a b) ((hw a b).differentiableAt (by norm_num))
      ha.differentiableAt ξ
  simp only [conn, hm]

theorem curv_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (ξ η : V n) :
    curv (fun x => H (φ x)) v ξ η = ∑ c, (fderiv ℂ φ v ξ) c • curv H (φ v) (coordVec c) (fderiv ℂ φ v η) := by
  rw [curv, mdbar_congr (conn_comp_eventually hφ h2 ξ)]
  have hd : DifferentiableAt ℂ φ v := hφ.differentiableAt
  have hf : ∀ c : Fin n, DifferentiableAt ℂ (fun x => (fderiv ℂ φ x ξ) c) v := by
    intro c
    have h1 : DifferentiableAt ℂ (fun x => fderiv ℂ φ x ξ) v :=
      hφ.fderiv.differentiableAt.clm_apply (differentiableAt_const ξ)
    exact (EuclideanSpace.proj (𝕜 := ℂ) c).differentiableAt.comp v h1
  have hc : ∀ (c : Fin n) (i j : r), DifferentiableAt ℝ (fun y => conn H y (coordVec c) i j) (φ v) :=
    fun c i j => (mContDiffAt_conn h2 hu (coordVec c)).diff i j
  ext i j
  simp only [Matrix.neg_apply, mdbar_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Finset.sum_neg_distrib]
  rw [dbar_sum (A := fun c x => (fderiv ℂ φ x ξ) c * conn H (φ x) (coordVec c) i j) (fun c _ => ((hf c).restrictScalars ℝ).mul
    ((hc c i j).comp v (hd.restrictScalars ℝ)))]
  rw [ContinuousLinearMap.sum_apply, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [dbar_mul (a := fun x => (fderiv ℂ φ x ξ) c) (b := fun x => conn H (φ x) (coordVec c) i j) ((hf c).restrictScalars ℝ) ((hc c i j).comp v (hd.restrictScalars ℝ)),
    dbar_eq_zero (hf c), dbar_comp_holo (u := fun y => conn H y (coordVec c) i j) (hc c i j) hd]
  simp [curv]

def substAlg (J : Matrix (Fin n) (Fin n) ℂ) :
    MvPolynomial (Fin n × Fin n) ℂ →ₐ[ℂ] MvPolynomial (Fin n × Fin n) ℂ :=
  aeval fun x : Fin n × Fin n => ∑ a, ∑ b, C (J x.1 a * starRingEnd ℂ (J x.2 b)) * X (a, b)

def jac (φ : V n → V n) (v : V n) : Matrix (Fin n) (Fin n) ℂ := fun c a => (fderiv ℂ φ v (coordVec a)) c

theorem curv_comp_coord {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (a b : Fin n) :
    curv (fun x => H (φ x)) v (coordVec a) (coordVec b) =
      ∑ c, ∑ d, (jac φ v c a * conj (jac φ v d b)) • curv H (φ v) (coordVec c) (coordVec d) := by
  rw [curv_comp hφ h2 hu]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [curv_eq_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [smul_smul]; rfl

theorem curvPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) :
    curvPoly (fun x => H (φ x)) v = (curvPoly H (φ v)).map (substAlg (jac φ v)) := by
  refine Matrix.ext fun i j => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [curvPoly, Matrix.of_apply, Matrix.map_apply, curv_comp_coord hφ h2 hu, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, map_sum, map_mul, substAlg, aeval_X, aeval_C, algebraMap_eq,
    Finset.sum_mul, Finset.mul_sum]
  simp_rw [← Fintype.sum_prod_type']
  let e : Fin n × Fin n × Fin n × Fin n ≃ Fin n × Fin n × Fin n × Fin n :=
    ⟨fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun x => (x.2.2.1, x.2.2.2, x.1, x.2.1), fun _ => rfl, fun _ => rfl⟩
  exact Fintype.sum_equiv e _ _ fun x => by simp only [e, Equiv.coe_fn_mk]; ring

theorem charpolyRev_map {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) {d : Type} [Fintype d]
    [DecidableEq d] (M : Matrix d d A) :
    (Matrix.charpolyRev M).map f = Matrix.charpolyRev (M.map f) := by
  unfold Matrix.charpolyRev
  rw [← Polynomial.coe_mapRingHom, RingHom.map_det]
  congr 1
  ext a b : 1
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem chernPoly_comp {H : V n → Matrix r r ℂ} {φ : V n → V n} {v : V n} (hφ : AnalyticAt ℂ φ v)
    (h2 : MContDiffAt 2 H (φ v)) (hu : IsUnit (H (φ v)).det) (k : ℕ) :
    chernPoly (fun x => H (φ x)) v k = substAlg (jac φ v) (chernPoly H (φ v) k) := by
  unfold chernPoly
  rw [curvPoly_comp hφ h2 hu]
  have hm : -(curvPoly H (φ v)).map (substAlg (jac φ v)) = (-curvPoly H (φ v)).map (substAlg (jac φ v)).toRingHom := by
    rw [Matrix.map_neg (f := (substAlg (jac φ v)).toRingHom) (fun a => map_neg _ a)]; rfl
  rw [hm, ← charpolyRev_map, Polynomial.coeff_map]
  rfl

theorem jac_eq_toMatrix (φ : V n → V n) (v : V n) :
    jac φ v = LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℂ).toBasis
      (EuclideanSpace.basisFun (Fin n) ℂ).toBasis (fderiv ℂ φ v : V n →ₗ[ℂ] V n) := by
  ext c a
  simp [LinearMap.toMatrix_apply, jac, coordVec]

end GlobalTheory.ChernPull


open ReciprocityTheory.L2DbarEstimates (V) in
theorem GlobalTheory.ChernPull.chernTop_comp : ∀ {n : ℕ} {ι : Type} {m : ι → ℕ} (R : MvPolynomial (ι × ℕ) ℝ) (K : ReciprocityTheory.L2DbarEstimates.V n → Mat m ℂ) (φ : ReciprocityTheory.L2DbarEstimates.V n → ReciprocityTheory.L2DbarEstimates.V n) (v : ReciprocityTheory.L2DbarEstimates.V n), AnalyticAt ℂ φ v → (∀ τ, MContDiffAt 2 (fun u => K u τ) (φ v)) → (∀ τ, IsUnit (K (φ v) τ).det) → chernTop R (fun w => K (φ w)) v = Complex.normSq (LinearMap.det (fderiv ℂ φ v : ReciprocityTheory.L2DbarEstimates.V n →ₗ[ℂ] ReciprocityTheory.L2DbarEstimates.V n)) * chernTop R K (φ v) := by
  intro n ι m R K φ v hφ h2 hu
  unfold chernTop
  have hc : ∀ x : ι × ℕ, chernPoly (fun u => K (φ u) x.1) v x.2 =
      GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v) (chernPoly (fun u => K u x.1) (φ v) x.2) :=
    fun x => GlobalTheory.ChernPull.chernPoly_comp hφ (h2 x.1) (hu x.1) x.2
  simp only [hc]
  have ha := congrArg (fun F => F R) (MvPolynomial.comp_aeval (R := ℝ)
    (f := fun x : ι × ℕ => chernPoly (fun u => K u x.1) (φ v) x.2)
    ((GlobalTheory.ChernPull.substAlg (GlobalTheory.ChernPull.jac φ v)).restrictScalars ℝ))
  simp only [AlgHom.comp_apply, AlgHom.coe_restrictScalars'] at ha
  rw [← ha, GlobalTheory.ChernPull.substAlg, GlobalTheory.T.topDegreeFormCoeff_linearSubst_eq_absDet_sq_mul, Complex.mul_conj, GlobalTheory.ChernPull.jac_eq_toMatrix,
    LinearMap.det_toMatrix, Complex.re_ofReal_mul]
  ring
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientDutyInPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

noncomputable section

namespace GlobalTheory.HeightCounting.Up.OPinAt

theorem mtInput_mtL {D : D7} (L : LocAll (lay0 D)) (M : MtFam D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (Q : D.what₂.places.Pl → Finset (PlE D.host)) (h : MtInput D M tup Q) : MtInput (withLoc L) (mtL L M) tup Q :=
  ⟨h.prod, h.para, h.uni, h.hyp, h.wt, h.rat, h.int, h.full⟩

theorem classSum_loc_of_sumTw {D : D7} {M : MtFam D} (h : SumTw D M) (i : D.nd.Loc) :
    GlobalTheory.CoefDuty.ClassSum (M.loc i) := by
  have e := D.nd.mu_w i
  have hs := h (D.nd.w i) (D.nd.w_tw i) (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2
  unfold MtFam.loc
  rw [e]
  exact hs

end GlobalTheory.HeightCounting.Up.OPinAt


end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CongrFunHeq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.HeightCounting.Up GlobalTheory.Mem.SRe GlobalTheory.Mem.R3.Rw
open GlobalTheory.HeightCounting GlobalTheory.Mem.R3.Tr

noncomputable section
namespace GlobalTheory.LayerMove
set_option maxHeartbeats 4000000
variable {D : D7} (m : Mv D)

def Mv.lam (x : GlobalTheory.LamTie.LamDat D) : GlobalTheory.LamTie.LamDat m.D := @_root_.GlobalTheory.LamTie.LamDat.mk (_)
    (C := @_root_.Formalism.L2.Host.CharFrame.mk (_)
      (P := (by with_unfolding_all exact (x.C.P :)))
      (W := (by with_unfolding_all exact (x.C.W :)))
      (mu0 := (by with_unfolding_all exact (x.C.mu0 :)))
      (eta := (by with_unfolding_all exact (x.C.eta :)))
      (chiPsi := (by with_unfolding_all exact (x.C.chiPsi :)))
      (del := (by with_unfolding_all exact (x.C.del :)))
      (del' := (by with_unfolding_all exact (x.C.del' :)))
      (isMu0 := (by with_unfolding_all exact (x.C.isMu0 :)))
      (isEta := (by with_unfolding_all exact (x.C.isEta :)))
      (isChi := (by with_unfolding_all exact (x.C.isChi :)))
      (isDel := (by with_unfolding_all exact (x.C.isDel :)))
      (isDel' := (by with_unfolding_all exact (x.C.isDel' :))))
    (q0 := (by with_unfolding_all exact (x.q0 :)))
    (w0 := (by with_unfolding_all exact (x.w0 :)))
    (c := (by with_unfolding_all exact (x.c :)))
    (chi := (by with_unfolding_all exact (x.chi :)))
theorem Mv.lam_ok {l : GlobalTheory.LamTie.LamDat D} (x : l.Ok) : (m.lam l).Ok := @_root_.GlobalTheory.LamTie.LamDat.Ok.mk (_) (_)
    (places := (by with_unfolding_all exact (x.places :)))
    (aux := (by with_unfolding_all exact (x.aux :)))
    (big := (by with_unfolding_all exact (x.big :)))
theorem Mv.lam_teich {l : GlobalTheory.LamTie.LamDat D} (x : l.Teich) : (m.lam l).Teich := (by with_unfolding_all exact (x :))
theorem Mv.lam_tie {l : GlobalTheory.LamTie.LamDat D} (x : GlobalTheory.LamTie.IsLamTieFull D.ntw l) : GlobalTheory.LamTie.IsLamTieFull m.D.ntw (m.lam l) := (by with_unfolding_all exact (x :))

theorem Mv.rowLoc {D : D7} (m : Mv D) {C : NChoice D} (a : NAllC D C) (F : Formalism.L2.RowFrame D) (F' : Formalism.L2.RowFrame m.D)
    (hF : HEq F'.rep F.rep) (x : Formalism.L2.RowLocTied D a.gal.lp F) : Formalism.L2.RowLocTied m.D (m.all a).gal.lp F' := by
  obtain ⟨rep, inj⟩ := F
  obtain ⟨rep', inj'⟩ := F'
  have e : rep' = (by with_unfolding_all exact (rep :)) := eq_of_heq ((by with_unfolding_all exact (hF :)))
  subst e
  exact (@_root_.Formalism.L2.RowLocTied.mk (_) (_) (_)
    (sat := (by with_unfolding_all exact (x.sat :)))
    )

theorem congrFun_heq {α β : Type} {f g : α → β} (h : HEq f g) (x : α) : f x = g x := by rw [eq_of_heq h]

end GlobalTheory.LayerMove
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySizesCongruencesHostFactsColumnChoices
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.HeightCounting.Up

theorem sizes_host_at_record : EvLgG fun K B f _ => KPx B f → ∀ (T : TwDat B) (w : ColW B f T) (Z : w.Lt), 100 ≤ (w.D Z).R.r ∧ (∀ k, 2 * (w.D Z).R.r ≤ (w.D Z).host.g k) ∧ RootsLL (w.D Z) ∧ SphericalInertData.HypEFK (w.D Z) ∧ SphericalInertData.HypCM (w.D Z) ∧ (∀ j, 1 ≤ j → j ≤ (w.D Z).R.m → ((w.D Z).sp.V j).IsDefinite) ∧ ∃ w0, GlobalTheory.LamTie.PlacesOk (w.D Z).host (AbsolutelyIrreducibleSpan.q0 (w.D Z)) w0 := by
  refine EvG.imp (_root_.GlobalTheory.Mem.RankSize.rank_ge_hundred.inter (_root_.GlobalTheory.Mem.Top.Bl.two_mul_r_le_g_level.inter (_root_.GlobalTheory.HeightCounting.Up.rootsLL_evLgG.inter (_root_.GlobalTheory.Mem.HostEFK.hypEFK_ev.inter (_root_.GlobalTheory.Mem.HypCMRec.hypCM_at_record.inter (_root_.GlobalTheory.Mem.DefSpaces.v_isDefinite.inter _root_.GlobalTheory.TwInputs.PlacesAt.evLgG_placesOk)))))) fun K _ _ _ _ H => ?_
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := H
  exact (h1.inter (h2.inter (h3.inter (h4.inter (h5.inter (h6.inter h7)))))).imp fun B f T _ G hk T' w Z =>
    ⟨G.1 hk T' w Z, G.2.1 hk T' w Z, G.2.2.1 hk T' w Z, G.2.2.2.1 hk T' w Z, G.2.2.2.2.1 hk T' w Z, G.2.2.2.2.2.1 hk T' w Z,
      G.2.2.2.2.2.2 hk T' w Z⟩

end GlobalTheory.HeightCounting.Up
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBaseOfFlagCpt
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.LieBase.exists_base_of_flagCpt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (T : TorModel Y) (F : Type) [Field F] (e : F ≃+* c.F) (σ : c.F →+* ℂ) (U : Formalism.L2.PjFree.Unf Xo c σ (Dw.p + Dw.q)), Formalism.L2.PjFree.GoodEmb c σ → Formalism.L2.PjFree.IsUnf U → ∀ (Φ : FlagTor T.Z e U) (k : U.Comp), ∃ (X : Var F) (j : X.X ⟶ gen T.Z) (f : (Φ.C k).Y.X ⟶ X.X) (f₀ : EigFrame T.Z (constF e X) (genericPt X ≫ j ≫ genι T.Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn) (E' : Fr (ratOf (Φ.C k).Y) Dw.mult Dw.mult) (φ : X.Fn →ₐ[F] (Φ.C k).Y.Fn), (j ≫ genStr T.Z ≫ spMap e.toRingHom = X.str) ∧ IsLieBase e (Φ.C k) X j f f₀ Eb A₀ ∧ Refines Eb E' φ f ∧ IsGraded E' (fun x : Root Dw.mult => (Φ.C k).gr x.1 x.2) := by
  intro E _ _ _ H Dw l Xo c O _ β Y T F _ e σ U hσ hU Φ k
  obtain ⟨X, j, hoi, hj, hr⟩ := _root_.GlobalTheory.CompOfVar.exists_var_comp E H Dw l Xo c O β T.Z F e T.smooth (Φ.C k).Y (Φ.C k).π (Φ.C k).π_str
  let f : (Φ.C k).Y.X ⟶ X.X := IsOpenImmersion.lift j (Φ.C k).π hr
  have hf : f ≫ j = (Φ.C k).π := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨f₀, Eb, A₀, hT⟩ := GlobalTheory.ShFam.TieBase.exists_tied E H Dw l Xo c O β T.Z F e X j hj
  have hcar := _root_.GlobalTheory.CarryAll.carries_everywhere E H Dw l Xo c O β T.Z F e σ _ U Φ k X j hoi hj f hf
  obtain ⟨E', φ, hR, hG⟩ := _root_.GlobalTheory.ShFam.BaseRefine.main E H Dw l Xo c O β T.Z F e (Φ.C k) X j hoi hj f hf f₀ Eb A₀ hT
    (fun K _ _ χ x hx g => hcar K χ x hx g)
  exact ⟨X, j, f, f₀, Eb, A₀, E', φ, hj, ⟨hoi, hf, hT⟩, hR, hG⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBelowOfRange
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr

noncomputable section

namespace GlobalTheory.Mem.R3.Rw.Untw

theorem exists_below_of_range (D D' : D7) (h : Set.range D.what₂.embLL ⊆ Set.range D'.what₂.embLL) (v' : D'.what₂.places.Pl) :
    ∃ v : D.what₂.places.Pl, Below D D' v v' := by
  first
  | exact @_root_.GlobalTheory.PrimeBelow.exists_below
  | exact _root_.GlobalTheory.PrimeBelow.exists_below
  | (apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply _root_.GlobalTheory.PrimeBelow.exists_below <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PrimeBelow.exists_below <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PrimeBelow.exists_below ..)

theorem resChar_of_below {D D' : D7} {v : D.what₂.places.Pl} {v' : D'.what₂.places.Pl} (hB : Below D D' v v') :
    D'.what₂.places.resChar v' = D.what₂.places.resChar v := by
  refine GlobalTheory.LvT.Inh.resChar_eq_of_mem_plEq D' v' (D.what₂.places.resChar_prime v) ((hB _ _ ?_).1 (GlobalTheory.LvT.Inh.resChar_mem_plEq D v))
  simp only [map_natCast]

end GlobalTheory.Mem.R3.Rw.Untw

namespace GlobalTheory.Mem.R3.Rw

end GlobalTheory.Mem.R3.Rw

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEigTrue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SCuspRows

theorem allSt_and' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h1 : AllSt p) (h2 : AllSt q) : AllSt fun K B f T w P x => p K B f T w P x ∧ q K B f T w P x :=
  EvG.imp (Step.and h1 h2) fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => ⟨(G a b c).1 w hw P x, (G a b c).2 w hw P x⟩

theorem allSt_mono' {p q : ∀ (K : Ctx) (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (P : Pre2 K w), St P → Prop}
    (h : AllSt p) (hq : ∀ K B f T w P x, p K B f T w P x → q K B f T w P x) : AllSt q :=
  EvG.imp h fun _ _ _ _ _ H => H.imp fun _ _ _ _ G a b c w hw P x => hq _ _ _ _ _ _ _ (G a b c w hw P x)


end GlobalTheory.SCuspRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingMapLargeCoefficientRings
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Formalism.L2.Fam.NPC Formalism.L2.Fam.NPC.BaseC GlobalTheory.HeckeLocN

theorem GlobalTheory.HeckeLocN.exists_twRing_of_large : ∀ (D : D7) (C : NChoice D) (F : TwFrameC D) (low : Finset ℕ) (E0 : PlEmb D.what₂), TwistFrameLowIndexCompatibility D F low → ChoiceC D C → ∀ w : D.what₂.places.Pl, ∃ F0 : Loc.FinExt (D.what₂.places.resChar w), ∀ (X : CoefIn D.what₂) (j : ℕ), X.E = E0 → F0.1 ≤ (X.Kx j w).1 → ∃ f : D.ntw.O0 (C.twI w) →+* OcC X j w, TwAlgAt C X j w f ∧ TwRdAt C X j w f ∧ (TwistedAt D w → ∀ (x : D.LL0) (y : D.ntw.O0 (C.twI w)), algebraMap (D.ntw.O0 (C.twI w)) (FractionRing (D.ntw.O0 (C.twI w))) y = (if C.sd w then D.ntw.emb0 (C.twI w) else D.ntw.emb0b (C.twI w)) x → ecC X j w (x : D.what₂.LL) = algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) := by
  intro D C F low E0 hT hC w
  obtain ⟨φ, hR, hn, ⟨K, hKf, hK⟩, halg⟩ :=
    GlobalTheory.HeightCounting.SameTw.exists_reads D C F hT w (D.what₂.places.resChar w) (C.twI_l w) (E0.emb w) (E0.emb_w w)
  refine ⟨⟨K, hKf⟩, ?_⟩
  intro X j hXE hle
  let g : D.ntw.O0 (C.twI w) →+* ↥(X.Kx j w).1 := φ.codRestrict (X.Kx j w).1 (fun y => hle (hK y))
  let f : D.ntw.O0 (C.twI w) →+* OcC X j w :=
    g.codRestrict (Loc.OL (X.Kx j w)) (fun y => (Formalism.BasicNotions.Examples₂.LB.mem_OL (X.Kx j w) (g y)).2 (hn y))
  have hf : ∀ y, iqC X j w (algebraMap (OcC X j w) (FractionRing (OcC X j w)) (f y)) = φ y := fun y => by
    rw [iqC_alg]; rfl
  have e1 : (iqC X j w).comp (ecC X j w) = E0.emb w := by
    ext x; rw [RingHom.comp_apply, iqC_ec, hXE]
  have e2 : (iqC X j w).comp ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) = φ := by
    ext y; exact hf y
  have hRd : GlobalTheory.HeightCounting.SameTw.Reads D C w (ecC X j w) ((algebraMap (OcC X j w) (FractionRing (OcC X j w))).comp f) :=
    GlobalTheory.HeightCounting.SameTw.Reads.of_comp (iqC X j w) (by rw [e1, e2]; exact hR)
  refine ⟨f, ?_, hRd, fun hw x y hy => GlobalTheory.HeightCounting.SameTw.Reads.emb hC hw hRd x y hy⟩
  intro z z' hz
  apply Subtype.val_injective
  apply Subtype.val_injective
  change φ _ = _
  rw [halg z z' hz]
  rfl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBlockDiagonalWithIdentity
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH IsDedekindDomain NumberField Formalism.L2 Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameBlockDiagonal

theorem rankV (D : D7) (k : Fin D.R.m) : (Vc D k).rank = D.R.nV := by
  rw [D.sp.V_rank _ (Nat.le_add_left _ _) k.2]

def IsBlockDiagonalWithIdentity {K : Type} [CommRing K] {n r : ℕ} (x : GL (Fin r) K) (y : GL (Fin n) K) : Prop :=
  ∀ a b : Fin n, y.val a b =
    if h : a.val < r ∧ b.val < r then x.val ⟨a.val, h.1⟩ ⟨b.val, h.2⟩ else if a = b then 1 else 0

end GlobalTheory.FrameBlockDiagonal

end
end

