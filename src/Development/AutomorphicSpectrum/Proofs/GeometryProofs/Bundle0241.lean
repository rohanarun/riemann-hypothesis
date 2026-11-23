module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0061
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0237
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0130
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyBadSt
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.KeyPBOfKeyOver
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
public import GroundTheory.HeightsAndTheta.Heights.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0090
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0152
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0186
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLogPeriodFamily
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsFamilyExponentialLocally
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0009
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0118
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PeriodLatticeSpans
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0131
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionPeriodsFiniteQuotient
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrix
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0147

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateOmegaCoherent
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HTCoh

theorem htOm_coherent : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E), (M.htOm L n).IsCohOn Set.univ ∧ ∀ q : Cpt ξ, (∀ u ∈ M.omLat q, n • u ∈ M.htOm L n q) ∧ M.htOm L n q ≤ M.omLat q ∧ ∀ (a : G ⟶ G) [IsMonHom a] (A : E →ₗ[Ω] E), M.IsDiffOf a A → ∀ w ∈ M.htOm L n q, w ∘ₗ A ∈ M.htOm L n q := by
  intro X _ Ω _ _ ξ hgen hnorm G _ hsemi L n hn hfull e hW E _ _ M
  have gen : ∀ (q : Cpt ξ) (x : Over.mk ξ ⟶ G) (w : Module.Dual Ω E),
      x ^ n = 1 → M.IsHTAt L n x q w → w ∈ M.htOm L n q := by
    intro q x w hx hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    exact Submodule.subset_span ⟨x, hx, hw⟩
  have mult : ∀ (q : Cpt ξ) (u : Module.Dual Ω E), u ∈ M.omLat q → n • u ∈ M.htOm L n q := by
    intro q u hu
    obtain ⟨⟨U, hqU, w, hw⟩, hdiff⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    have h1 : (1 : Over.mk ξ ⟶ G) ^ n = 1 := one_pow n
    have h0 : M.IsHTAt L n 1 q (w 1) := hw 1 h1 q hqU
    have h2 : M.IsHTAt L n 1 q (w 1 + n • u) := (hdiff 1 (w 1) _ h1 h0).2 ⟨u, hu, rfl⟩
    have hsub := Submodule.sub_mem _ (gen q 1 _ h1 h2) (gen q 1 _ h1 h0)
    rwa [add_sub_cancel_left] at hsub
  refine ⟨?_, fun q => ⟨fun u hu => mult q u hu, ?_, ?_⟩⟩
  · intro p _
    haveI := hsemi
    haveI : IsCommMonObj G := IsSemiAbelian.comm
    have hsm : AlgebraicGeometry.Smooth G.hom := IsSemiAbelian.smooth
    obtain ⟨-, hVB⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_isVB_of_smooth X Ω ξ G E M hgen hsm
    obtain ⟨U2, hpU2, bv, -, hfr⟩ := hVB p (Set.mem_univ p)
    obtain ⟨⟨U1, hpU1, w, hw⟩, -⟩ :=
      _root_.GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M p
    haveI : Finite {x : Over.mk ξ ⟶ G // x ^ n = 1} := hW.finite
    obtain ⟨k, ⟨eqv⟩⟩ := Finite.exists_equiv_fin {x : Over.mk ξ ⟶ G // x ^ n = 1}
    let b1 : Fin k → Module.Dual Ω E := fun i => w (eqv.symm i).1
    let b2 : Fin (Module.finrank Ω E) → Module.Dual Ω E := fun j => n • bv j
    refine ⟨U1 ⊓ U2, TopologicalSpace.Opens.mem_inf.2 ⟨hpU1, hpU2⟩, k + Module.finrank Ω E, Fin.append b1 b2, ?_⟩
    intro q _ hqU
    have hq1 := (TopologicalSpace.Opens.mem_inf.1 hqU).1
    have hq2 := (TopologicalSpace.Opens.mem_inf.1 hqU).2
    obtain ⟨-, hframe⟩ := hfr q (Set.mem_univ q) hq2
    obtain ⟨-, hdiff⟩ := _root_.GlobalTheory.CompanionTheory.Ar.htLat_exists_lifts X Ω ξ hgen hnorm G hsemi L n hn hfull e hW E M q
    apply le_antisymm
    · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
      refine Submodule.span_le.mpr ?_
      rintro w' ⟨y, hy, hyw'⟩
      have hwy : M.IsHTAt L n y q (w y) := hw y hy q hq1
      obtain ⟨u, hu, rfl⟩ := (hdiff y (w y) w' hy hwy).1 hyw'
      refine Submodule.add_mem _ ?_ ?_
      · apply Submodule.subset_span
        refine ⟨Fin.castAdd _ (eqv ⟨y, hy⟩), ?_⟩
        simp [b1, Fin.append_left]
      · rw [hframe] at hu
        clear hyw'
        induction hu using Submodule.span_induction with
        | mem v hv =>
          obtain ⟨j, rfl⟩ := hv
          apply Submodule.subset_span
          exact ⟨Fin.natAdd k j, by simp [b2, Fin.append_right]⟩
        | zero => rw [smul_zero]; exact Submodule.zero_mem _
        | add v1 v2 _ _ h1 h2 => rw [smul_add]; exact Submodule.add_mem _ h1 h2
        | smul r v _ h => rw [smul_comm]; exact Submodule.smul_mem _ r h
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      induction i using Fin.addCases with
      | left i =>
        rw [Fin.append_left]
        exact gen q _ _ (eqv.symm i).2 (hw _ (eqv.symm i).2 q hq1)
      | right j =>
        rw [Fin.append_right]
        exact mult q _ (by rw [hframe]; exact Submodule.subset_span ⟨j, rfl⟩)
  · simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm]
    refine Submodule.span_le.mpr ?_
    rintro w ⟨x, -, hw⟩
    exact hw.1
  · intro a _ A hA w hw
    simp only [GlobalTheory.CompanionTheory.Ar.LieModel.htOm] at hw ⊢
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, hxw⟩ := hw
      obtain ⟨y', hy', hrel⟩ := hW.perfect (fun g => e x (g ≫ a)) (by
        intro g g' hg hg'
        show e x ((g * g') ≫ a) = e x (g ≫ a) * e x (g' ≫ a)
        rw [MonObj.mul_comp]
        exact hW.mul_right x _ _ hx (by rw [← MonObj.pow_comp, hg, MonObj.one_comp])
          (by rw [← MonObj.pow_comp, hg', MonObj.one_comp]))
      exact Submodule.subset_span ⟨y', hy', _root_.GlobalTheory.CompanionTheory.Ar.LieModel.isHTAt_end X Ω ξ hgen hnorm G hsemi L n hn hfull e hW
        E M a A hA x y' hx hy' (fun g hg => (hrel g hg).symm) q w hxw⟩
    | zero => rw [LinearMap.zero_comp]; exact Submodule.zero_mem _
    | add w1 w2 _ _ h1 h2 => rw [LinearMap.add_comp]; exact Submodule.add_mem _ h1 h2
    | smul r w _ h =>
      have hc : (r • w) ∘ₗ A = r • (w ∘ₗ A) := LinearMap.ext fun _ => rfl
      rw [hc]; exact Submodule.smul_mem _ r h

end GlobalTheory.CompanionTheory.Ar.HTCoh
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.KeyInputFromPpData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum

section Lie

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {E : Type} [AddCommGroup E] [Module R E]

def epsIso (R : Type) [CommRing R] : epsR R ≅ epsAt (𝟙 (Sp R)) :=
  Over.isoMk (Iso.refl _) (by simp [spMap])

def tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : epsR R ⟶ G := (epsIso R).hom ≫ M.pt x

theorem tanVec_left (M : LieModel G (𝟙 (Sp R)) E) (x : E) : (tanVec M x).left = (M.pt x).left := by
  simp [tanVec, epsIso]

theorem one_left : (1 : Over.mk (𝟙 (Sp R)) ⟶ G).left = η[G].left := by
  rw [Hom.one_def, Over.comp_left]
  have h : (toUnit (Over.mk (𝟙 (Sp R)))).left = 𝟙 _ := by
    have := Over.w (toUnit (Over.mk (𝟙 (Sp R))))
    simpa using this
  rw [h]
  exact Category.id_comp _

theorem isTangent_tanVec (M : LieModel G (𝟙 (Sp R)) E) (x : E) : IsTangent (tanVec M x) := by
  have h := M.tan x
  unfold IsTangent
  rw [tanVec_left]
  exact h.trans one_left

theorem exists_tanVec (M : LieModel G (𝟙 (Sp R)) E) (w : epsR R ⟶ G) (hw : IsTangent w) : ∃ x, tanVec M x = w := by
  obtain ⟨x, hx⟩ := M.onto ((epsIso R).inv ≫ w) (by
    unfold IsTanAt
    have e : ((epsIso R).inv ≫ w).left = w.left := by simp [epsIso]
    rw [e]
    exact Eq.trans hw one_left.symm)
  exact ⟨x, by rw [tanVec, hx]; simp⟩

theorem tanVec_injective (M : LieModel G (𝟙 (Sp R)) E) : Function.Injective (tanVec M) := fun a b h =>
  M.inj (Over.OverMorphism.ext (by rw [← tanVec_left, ← tanVec_left, h]))

theorem prod_ofFn_tanVec (M : LieModel G (𝟙 (Sp R)) E) :
    ∀ {n : ℕ} (f : Fin n → E), (List.ofFn fun j => tanVec M (f j)).prod = tanVec M (∑ j, f j)
  | 0, f => by simp [tanVec, M.pt_zero]
  | n + 1, f => by
    rw [List.ofFn_succ, List.prod_cons, prod_ofFn_tanVec M, Fin.sum_univ_succ]
    simp only [tanVec, M.add, MonObj.comp_mul]

theorem isLieComb_tanVec_iff (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (c : Fin n → R) (x : E) :
    IsLieComb c (fun i => tanVec M (b i)) (tanVec M x) ↔ x = ∑ i, c i • b i := by
  have hs : ∀ i, (tanVec M (c i • b i)).left = spMap (epsScaleR (c i)) ≫ (tanVec M (b i)).left := fun i => by
    rw [tanVec_left, tanVec_left, M.smul]
    rfl
  constructor
  · rintro ⟨u, hu, hw⟩
    have hu' : u = fun i => tanVec M (c i • b i) := funext fun i =>
      Over.OverMorphism.ext ((hu i).trans (hs i).symm)
    rw [hu', prod_ofFn_tanVec M] at hw
    exact tanVec_injective M hw
  · rintro rfl
    exact ⟨fun i => tanVec M (c i • b i), hs, (prod_ofFn_tanVec M _).symm⟩

theorem isLieBasis_tanVec (M : LieModel G (𝟙 (Sp R)) E) {n : ℕ} (b : Fin n → E) (hli : LinearIndependent R b)
    (hsp : Submodule.span R (Set.range b) = ⊤) : IsLieBasis (fun i => tanVec M (b i)) := by
  refine ⟨fun i => isTangent_tanVec M _, fun w hw => ?_⟩
  obtain ⟨x, rfl⟩ := exists_tanVec M w hw
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp ▸ Submodule.mem_top : x ∈ Submodule.span R (Set.range b))
  refine ⟨c, (isLieComb_tanVec_iff M b c x).2 hc.symm, fun c' h => ?_⟩
  have h' := (isLieComb_tanVec_iff M b c' x).1 h
  have h0 : ∑ i, (c' i - c i) • b i = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib, ← h', hc, sub_self]
  funext i
  exact sub_eq_zero.1 (Fintype.linearIndependent_iff.1 hli _ h0 i)

end Lie

section Sec

variable {X : Scheme.{0}}

theorem mem_basicOpen_map {U V : X.Opens} (h : V ≤ U) (f : Γ(X, U)) (y : X) :
    y ∈ X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) ↔ y ∈ V ∧ y ∈ X.basicOpen f := by
  have e : X.basicOpen ((X.presheaf.map (homOfLE h).op).hom f) = V ⊓ X.basicOpen f :=
    Scheme.basicOpen_res X f (homOfLE h).op
  rw [e]
  rfl

theorem sameSec_ofPow {L : LB X} (s : Out.H0 L 1) : KeyDeg.SameSec s (GlobalTheory.GeneratorFrame.ofPow s) := fun _ => rfl

theorem nonzeroLocus_ofPow {L : LB X} (s : Out.H0 L 1) {y : X} (hy : y ∈ Out.nonzeroLocus s) :
    y ∈ Out.nonzeroLocus (GlobalTheory.GeneratorFrame.ofPow s) := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, rfl⟩ : ∃ i, k = fun _ => i := ⟨k 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  have hU : y ∈ L.U i := GlobalTheory.GeneratorFrame.wchart_le' L (fun _ => i) (X.basicOpen_le _ hk)
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, (mem_basicOpen_map _ _ y).2 ⟨hU, hk⟩⟩

end Sec

section Main

theorem dualMapR_eq {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Chart.dualMapR f = dualMap f := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR, dualMap]

theorem mem_basicOpen_appLE {X Y : Scheme.{0}} (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (h : V ≤ φ ⁻¹ᵁ U) (f : Γ(X, U))
    {z : Y} (hz : z ∈ V) (hy : φ z ∈ X.basicOpen f) : z ∈ Y.basicOpen ((φ.appLE U V h).hom f) := by
  have e : (φ.appLE U V h).hom f = (Y.presheaf.map (homOfLE h).op).hom ((φ.app U).hom f) := rfl
  rw [e]
  refine (mem_basicOpen_map h _ z).2 ⟨hz, ?_⟩
  rw [← Scheme.preimage_basicOpen]
  exact hy

theorem exists_keyIn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L), 1 ≤ D.g → ∀ (s : Out.H0 D.t.PP.L 1) (e : Fin D.g → D.B.carrier), KeyDeg.NonVan D.t.G.hom s → LinearIndependent (𝓞 L) e → Submodule.span (𝓞 L) (Set.range e) = ⊤ → ∃ (x : KeyIn L) (th : D.t.PP.L.Sec) (hg : x.P.g = D.g) (v : Fin x.P.g → (epsR (𝓞 L) ⟶ D.t.G)), KeyDeg.SameSec s th ∧ KeyDeg.NonVan D.t.G.hom th ∧ KeyOver (algebraMap (𝓞 L) L) D.t th x v ∧ IsLieBasis v ∧ ∀ i, (v i).left = (D.MB.pt (e (i.cast hg))).left := by
  intro E _ _ _ H L _ _ D hg s e hs hli hsp
  have sm := D.tK.semi.smooth
  have gc := D.tK.semi.geomConnected
  have : ConnectedSpace D.tK.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := D.tK.G.hom) (𝟙 _) (𝟙 _) D.tK.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  have hnv : KeyDeg.NonVan D.t.G.hom (GlobalTheory.GeneratorFrame.ofPow s) := fun b => by
    obtain ⟨y, hy, hy'⟩ := hs b
    exact ⟨y, hy, nonzeroLocus_ofPow s hy'⟩
  have hv := isLieBasis_tanVec D.MB e hli hsp
  obtain ⟨v', hv', hφ⟩ := GlobalTheory.exists_isLieBasis_baseChange (𝓞 L) L (algebraMap (𝓞 L) L) D.t.G D.tK.G D.m.φ D.m.cart
    D.t.semi.smooth D.g _ hv
  obtain ⟨d, hd⟩ := exists_dim_of_preconnected D.tK.G.hom (eSec D.tK.G (default : PrimeSpectrum L))
  obtain ⟨u, hu⟩ := GlobalTheory.CM.TenDim.exists_isLieBasis D.tK.G hd
  have hdg : d = D.g := GlobalTheory.KeyFramePoint.card_eq_of_isLieBasis D.m.cart hu hv'
  rw [hdg] at hd
  obtain ⟨hp, ha, hk⟩ := D.princ
  obtain ⟨w, hw, hr, -⟩ := D.m.lin
  have hw' := (isGen_iff w).1 hw
  obtain ⟨xth, hx⟩ := sec_pull_down hw' D.t.PP.isLB D.tK.PP.isLB (GlobalTheory.GeneratorFrame.ofPow s)
  have hcompat : ∀ (j : (D.t.PP.L.pull D.m.φ).ι) (i : D.tK.PP.L.ι)
      (h : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U (j PUnit.unit)),
      (D.m.φ.appLE _ _ h).hom ((GlobalTheory.GeneratorFrame.ofPow s).f (j PUnit.unit)) =
        (show Γ(D.tK.G.left, (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i) from (w.s (j, i)).val) *
          resG _ inf_le_right (xth.f i) := fun j i h => fn_ext fun y hy =>
    (gs_appLE D.m.φ _ _ h (𝟙 _) y hy _).trans ((hx _ (𝟙 _) y _ i (h hy) hy.2).trans
      (Eq.symm ((gs_mul (𝟙 _) y _ hy _ _).trans
        (congrArg₂ (· * ·) (gs_unit (𝟙 _) y _ hy _) (gs_res (𝟙 _) y _ hy _)))))
  have hne : ∀ s₀ : Sp L, ∃ z : D.tK.G.left, D.tK.G.hom z = s₀ ∧ z ∈ Out.nonzeroLocus xth := fun s₀ => by
    obtain ⟨y, hy, hyn⟩ := hnv (spMap (algebraMap (𝓞 L) L) s₀)
    obtain ⟨z, rfl, hz⟩ := Scheme.exists_preimage_of_isPullback D.m.cart.1 y s₀ hy
    obtain ⟨l, hl⟩ := TopologicalSpace.Opens.mem_iSup.1 hyn
    obtain ⟨i, hi⟩ := exists_chart D.tK.PP.isLB z
    have hU : D.m.φ z ∈ D.t.PP.L.U l := Scheme.basicOpen_le _ _ hl
    let j : PUnit → D.t.PP.L.ι := fun _ => l
    have hV : z ∈ (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i := ⟨mem_pull.2 hU, hi⟩
    have hle : (D.t.PP.L.pull D.m.φ).U j ⊓ D.tK.PP.L.U i ≤ D.m.φ ⁻¹ᵁ D.t.PP.L.U l := fun _ hy => mem_pull.1 hy.1
    have h1 := mem_basicOpen_appLE D.m.φ hle _ hV hl
    have e := hcompat j i hle
    refine ⟨z, hz, TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩⟩
    change z ∈ D.tK.G.left.basicOpen ((D.m.φ.appLE _ _ hle).hom _) at h1
    rw [e, Scheme.basicOpen_mul] at h1
    exact ((mem_basicOpen_map _ _ z).1 h1.2).2
  obtain ⟨-, ws, gs', -⟩ := D.tK.sym
  refine ⟨KeyBadModel.keyInOf D.tK xth D.g hg v' hv' ⟨inferInstance, sm, hp, gc⟩ hd
    (fun _ => ⟨⊤, trivial, gen_of_iso ((isGen_iff ws).1 gs') _⟩) ha hk hne, GlobalTheory.GeneratorFrame.ofPow s, rfl,
    fun i => tanVec D.MB (e i), sameSec_ofPow s, hnv, ?_, hv, fun i => tanVec_left _ _⟩
  have he : eSec D.tK.G ≫ D.m.φ = spMap (algebraMap (𝓞 L) L) ≫ eSec D.t.G := by
    have := D.m.cm.e_comm
    rwa [D.m.base] at this
  have hrig : ∀ (e' : (𝟙_ (Over (Sp L))).left ⟶ (𝟙_ (Over (Sp (𝓞 L)))).left) (he' : eSec D.tK.G ≫ D.m.φ = e' ≫ eSec D.t.G),
      e' = D.m.cm.e → rigPullOf D.m.φ e' he' D.t.PP.L D.t.PP.rig = D.m.cm.rigPull D.t.PP.L D.t.PP.rig := by
    rintro _ _ rfl
    rfl
  refine ⟨D.m.φ, he, w, D.m.cart, hw, ?_, hcompat, fun i => ?_⟩
  · have h2 : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec D.tK.G) (fun _ => 1)) D.tK.PP.rig
        (rigPullOf D.m.φ (spMap (algebraMap (𝓞 L) L)) he D.t.PP.L D.t.PP.rig) := by
      rw [hrig _ he D.m.base.symm]
      exact hr
    exact h2
  · exact (hφ i).trans (by rw [dualMapR_eq])

end Main

end GlobalTheory.CompanionTheory.Ar.Sl.KeyDatum
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodsRiemannForm
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open _root_.GlobalTheory.CompanionTheory.Ar.Flat.Link _root_.GlobalTheory.CompanionTheory.Ar.Flat.Link

theorem exists_logPeriods_isRiem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ (ρ : ℝ) (Λ : Type) (_ : AddCommGroup Λ) (L : LogPeriods n a C.g Λ), 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ punct n a 1, C.IsRiem ((ρ : ℂ) • z) (L.H z) := by
  intro E _ _ _ H D l Xo σ n a C hpq hσ
  obtain ⟨g', ty, hty⟩ := GlobalTheory.AllClasses.exists_isTypeFn H D.p D.q
  obtain ⟨FU⟩ := GlobalTheory.familyUnif_of_laws GlobalTheory.abelianSchemeLaws_all.1 E H D l Xo σ g' ty hpq hσ hty
  have hsemi : IsSemiAbelian C.t.G := C.t.semi
  obtain ⟨ε, hε, hεB, ⟨e₀⟩⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_famExp_near C.R C.t.G C.g n C.M (Metric.ball 0 1) C.ψ hsemi.smooth C.hol 0
    (Metric.mem_ball_self one_pos)
  have h0ε : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ε := Metric.mem_ball_self hε
  obtain ⟨Γ₀, hΓ₀, -, hfin, hfree⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.FamExp.per_discrete C.R C.t.G C.g n C.M _ C.ψ e₀ 0 h0ε
  let Q : (Fin n → ℂ) → AddSubgroup (Fin C.g → ℂ) := fun b => AddSubgroup.closure (e₀.per b)
  have hQ : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε, ∀ p, p ∈ Q b ↔ p ∈ e₀.per b := fun b hb p =>
    mem_closure_per e₀ hb p
  have hsp : ∀ x : Γ₀, ∃ (ε' : ℝ) (s : (Fin n → ℂ) → (Fin C.g → ℂ)), 0 < ε' ∧
      DifferentiableOn ℂ s (Metric.ball 0 ε') ∧ s 0 = x ∧ ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ε', s b ∈ Q b := by
    intro x
    obtain ⟨ε', s, h0, hsub, hd, hs0, hs⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.per_spreads C.R C.t.G C.g n C.M _ C.ψ e₀ Metric.isOpen_ball 0 h0ε x
      (by rw [← hΓ₀]; exact x.2)
    exact ⟨ε', s, h0, hd, hs0, fun b hb => (hQ b (hsub hb) _).2 (hs b hb)⟩
  obtain ⟨ρ, hρ0, hρc, S, hSd, hS0, hSa, hSq⟩ := exists_additive_sections Γ₀ Q (min 1 ε) (lt_min one_pos hε) hsp
  have hρ1 : ρ ≤ 1 := hρc.trans (min_le_left _ _)
  have hball : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (hρc.trans (min_le_right _ _))
  have hball1 : Metric.ball (0 : Fin n → ℂ) ρ ⊆ Metric.ball 0 1 := Metric.ball_subset_ball hρ1
  have h0ρ : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ := Metric.mem_ball_self hρ0
  let e : FamExp C.t.G C.M (Metric.ball 0 ρ) C.ψ := restrict e₀ Metric.isOpen_ball hball
  have hQ' : ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ p, p ∈ Q b ↔ p ∈ e.per b := fun b hb p => hQ b (hball hb) p
  have hΓ₀' : (Γ₀ : Set (Fin C.g → ℂ)) = e.per 0 := hΓ₀
  have hSp : ∀ x, ∀ b ∈ Metric.ball (0 : Fin n → ℂ) ρ, S x b ∈ e.per b := fun x b hb =>
    (hQ' b hb _).1 (hSq x b hb)
  obtain ⟨i, Hf, hrank, hopen, hloc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_marking E H D l Xo σ n a C g' ty FU ρ e hρ0 hρ1
  obtain ⟨hfreeL, hfinL, -⟩ := GlobalTheory.Coisotropic.lattice_rank E H (FU.Di i)
  have hU : ∀ z ∈ punct n a 1, (ρ : ℂ) • z ∈ punct n a ρ := fun z hz => (smul_mem_punct hρ0).2 hz
  have hsm : Differentiable ℂ (fun z : Fin n → ℂ => (ρ : ℂ) • z) := differentiable_id.fun_const_smul _
  have key : ∃ L : LogPeriods n a C.g (FU.Di i).La, L.H = (fun z => Hf ((ρ : ℂ) • z)) := by
    refine _root_.GlobalTheory.CompanionTheory.Ar.Flat.exists_logPeriods_of_local_markings n a C.g C.a_le (FU.Di i).La (FU.Di i).EF (fun z => Q ((ρ : ℂ) • z))
      (fun z => Hf ((ρ : ℂ) • z)) (punct n a 1) Γ₀ (fun x z => S x ((ρ : ℂ) • z)) rfl hrank (FU.Di i).alt
      (FU.Di i).unimod ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact fun z hz => ⟨(hopen _ (hU z hz)).1, fun x hx => (hopen _ (hU z hz)).2.1 x hx⟩
    · intro z₀ hz₀
      obtain ⟨N, hNo, hzN, hNp, P, hPd, hP⟩ := hloc _ (hU z₀ hz₀)
      refine ⟨(fun z => (ρ : ℂ) • z) ⁻¹' N, hNo.preimage hsm.continuous, hzN,
        fun z hz => (smul_mem_punct hρ0).1 (hNp hz), fun z => P ((ρ : ℂ) • z), fun x => ?_, fun z hz => ?_⟩
      · exact (hPd x).comp hsm.differentiableOn (fun z hz => hz)
      · obtain ⟨h1, h2, h3⟩ := hP _ hz
        refine ⟨h1, ?_, h3⟩
        ext p
        have h4 : p ∈ (P ((ρ : ℂ) • z)).range ↔ p ∈ e.per ((ρ : ℂ) • z) := by
          rw [← SetLike.mem_coe, h2]
        rw [h4]
        exact (hQ' _ (punct_subset_ball (hNp hz)) p).symm
    · intro x
      refine ⟨(hSd x).comp hsm.differentiableOn (fun z hz => smul_mem_ball hρ0 hz), ?_,
        fun z hz => hSq x _ (smul_mem_ball hρ0 hz.1)⟩
      show S x ((ρ : ℂ) • 0) = x
      rw [smul_zero]
      exact hS0 x
    · exact fun x y z => hSa x y _
    · intro s hs hsU
      obtain ⟨u, hu, huU⟩ := exists_seq_punct (n := n) (a := a)
      have hρc' : (ρ : ℂ) ≠ 0 := by exact_mod_cast hρ0.ne'
      have htend : Tendsto (fun k => (ρ : ℂ) • u k) atTop (𝓝 0) := by
        have h := hu.const_smul (ρ : ℂ)
        rwa [smul_zero] at h
      have hcl := _root_.GlobalTheory.CompanionTheory.Ar.Flat.mem_per_of_frequently C.R C.t.G C.g n C.M (Metric.ball 0 ρ) C.ψ e hsemi.separated
        ⟨Metric.isOpen_ball, fun r => (C.hol.2 r).mono hball1⟩ 0 h0ρ (fun b => s ((ρ : ℂ)⁻¹ • b))
        (ContinuousAt.comp_of_eq hs (continuous_const_smul _).continuousAt (smul_zero _))
        (htend.frequently (Eventually.frequently (Eventually.of_forall fun k => by
          refine ⟨punct_subset_ball (hU _ (huU k)), ?_⟩
          show s ((ρ : ℂ)⁻¹ • (ρ : ℂ) • u k) ∈ e.per ((ρ : ℂ) • u k)
          rw [smul_smul, inv_mul_cancel₀ hρc', _root_.one_smul]
          exact (hQ' _ (punct_subset_ball (hU _ (huU k))) _).1 (hsU _ (huU k)))))
      have h0 : s 0 ∈ e.per 0 := by simpa using hcl
      rw [← hΓ₀'] at h0
      exact h0
    · rw [hΓ₀']
      exact _root_.GlobalTheory.CompanionTheory.Ar.Flat.span_per_eq_top C.R C.t.G C.g n C.M _ C.ψ e hsemi 0 h0ρ
    · intro N hN
      obtain ⟨T, hT, hTw⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.toric_torsion_radical_period E H C.R C.t C.g n C.M (Metric.ball 0 ρ) C.ψ e C.dim 0 h0ρ Γ₀ hΓ₀' N hN
      refine ⟨T, hT, fun x y hx z hz => ?_⟩
      have hb := hU z hz
      have hbm := punct_subset_ball hb
      have hc := cubWeil_carry e hρ0 N hN (S x) (S y) (hSd x) (hSd y) (hSp x) (hSp y) 1 (by
        rw [hS0 x, hS0 y]
        have h1 : unitOn (1 : ℂˣ) = 1 := map_one _
        rw [h1]
        exact hTw x y hx) _ hbm
      have hz' := (hopen _ hb).2.2.2 N 1 hN _ (hSp x _ hbm) _ (hSp y _ hbm) hc
      exact exists_int_of_exp_eq_one hN hz'
  obtain ⟨L, hLH⟩ := key
  refine ⟨ρ, (FU.Di i).La, inferInstance, L, hρ0, hρ1, fun z hz => ?_⟩
  rw [hLH]
  exact (hopen _ (hU z hz)).2.2.1

end GlobalTheory.CompanionTheory.Ar.Flat
end
end

