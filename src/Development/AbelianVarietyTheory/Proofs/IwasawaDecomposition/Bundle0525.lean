module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PerValNeZero
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0025
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0016
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0011
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0010
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Bundle0001
public import Development.AbelianVarietyTheory.Statements.HeightBoundStatement.HTBoundSt
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0038
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Matrix CategoryTheory.Obj Topology
open Filter GlobalTheory.HolHom

namespace GlobalTheory.ShFam.HorLift

section General

variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isHolTo_of_comp_open {X Y : Scheme.{0}} (i : X ⟶ Y) [IsOpenImmersion i] {B : Set V} {y : V → (Sp ℂ ⟶ X)}
    (h : IsHolTo B fun b => y b ≫ i) : IsHolTo B y := by
  intro U f
  have key : ∀ (U' : X.Opens) (_ : i ⁻¹ᵁ (i ''ᵁ U) = U') (f : Γ(X, U')), IsOpen {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} ∧
      DifferentiableOn ℂ (fun b => valAt' (y b) U' f) {b ∈ B | ⊤ ≤ y b ⁻¹ᵁ U'} := by
    rintro _ rfl f
    have : IsIso (i.app (i ''ᵁ U)) := i.isIso_app _ (i.image_le_opensRange U)
    obtain ⟨g, rfl⟩ := (ConcreteCategory.bijective_of_isIso (i.app (i ''ᵁ U))).2 f
    have := h (i ''ᵁ U) g
    simp only [valAt'_eq_valR, valR_comp] at this
    exact this
  exact key U (i.preimage_image_eq U) f

theorem differentiableAt_dir [FiniteDimensional ℂ V] {G' G₀ G₁ S' S₀ S₁ : Scheme.{0}} {φ₀ : G' ⟶ G₀} {φ₁ : G' ⟶ G₁}
    {p : G' ⟶ S'} {p₀ : G₀ ⟶ S₀} {p₁ : G₁ ⟶ S₁} {f₀ : S' ⟶ S₀} {f₁ : S' ⟶ S₁} (H₀ : IsPullback φ₀ p p₀ f₀)
    (H₁ : IsPullback φ₁ p p₁ f₁) {g : ℕ} {B : Set V} {y : V → (Sp ℂ ⟶ S')} (hy : IsHolTo B y)
    {ex : V → (Fin g → ℂ) → (Sp ℂ ⟶ G₀)}
    (hex : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => ex bz.1 bz.2)
    (hover : ∀ b ∈ B, ∀ w, ex b w ≫ p₀ = y b ≫ f₀) {b₀ : V} (hb₀ : b₀ ∈ B)
    (hinj : ∀ w, IsDerivAt (ex b₀) 0 w (constVec (ex b₀ 0)) → w = 0) {v : V → (Sp (DualNumber ℂ) ⟶ G₁)}
    (hv : HolTan B v) {W : V → Fin g → ℂ}
    (hW : ∀ b ∈ B, ∃ v₀ : Sp (DualNumber ℂ) ⟶ G', v₀ ≫ p = constVec (y b) ∧ v₀ ≫ φ₁ = v b ∧
      IsDerivAt0 (ex b) (W b) (v₀ ≫ φ₀)) : DifferentiableAt ℂ W b₀ := by
  haveI : Nonempty (Sp ℂ ⟶ G') := ⟨H₀.lift _ _ (hover b₀ hb₀ 0)⟩
  choose! e h₀ hp using fun b (hb : b ∈ B) w =>
    (⟨H₀.lift _ _ (hover b hb w), H₀.lift_fst _ _ _, H₀.lift_snd _ _ _⟩ :
      ∃ x : Sp ℂ ⟶ G', x ≫ φ₀ = ex b w ∧ x ≫ p = y b)
  have hO := isOpen_of_isHolTo hex
  have he : IsHolTo (B ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 := by
    have h1 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ φ₀) hex
      fun bz hb => h₀ _ hb.1 _
    have h2 := LocLift.isHolTo_congr (y' := fun bz : V × (Fin g → ℂ) => e bz.1 bz.2 ≫ p)
      (LocLift.isHolTo_comp hy hO differentiableOn_fst fun _ hb => hb.1) fun bz hb => hp _ hb.1 _
    exact isHolTo_of_holAt hO fun z hz =>
      holAt_of_isPullback H₀ (holAt_of_isHolTo h1 hz) (holAt_of_isHolTo h2 hz)
  have hsl : ∀ b ∈ B, HolAt (e b) 0 := fun b hb =>
    (holAt_of_isHolTo he (z := (b, 0)) ⟨hb, trivial⟩).precomp (k := fun z => (b, z)) (by fun_prop)
  have hder : ∀ b ∈ B, ∀ w, ∃ u, IsDerivAt (e b) 0 w u ∧ IsDerivAt (ex b) 0 w (u ≫ φ₀) ∧
      u ≫ p = constVec (y b) := fun b hb w => by
    obtain ⟨u, hu⟩ := (hsl b hb).exists_isDerivAt w
    have h1 := hu.comp φ₀
    have h2 := hu.comp p
    simp only [h₀ b hb, hp b hb] at h1 h2
    exact ⟨u, hu, h1, h2.unique (isDerivAt_const _ _ _)⟩
  have hv' : ∀ b ∈ B, IsDerivAt (fun w => e b w ≫ φ₁) 0 (W b) (v b) := fun b hb => by
    obtain ⟨v₀, a1, a2, a3⟩ := hW b hb
    obtain ⟨u, hu, h1, h2⟩ := hder b hb (W b)
    obtain rfl : u = v₀ := H₀.hom_ext (h1.unique ((isDerivAt0_iff _ _ _).1 a3)) (h2.trans a1.symm)
    exact a2 ▸ hu.comp φ₁
  have he₁ := LocLift.isHolTo_comp_hom he φ₁
  refine HolLieFrame.differentiableAt_of_forms _ b₀ fun w hw => hinj w ?_
  obtain ⟨u, hu, h1, h2⟩ := hder b₀ hb₀ w
  have h3 : IsDerivAt (fun w => e b₀ w ≫ φ₁) 0 w (constVec (e b₀ 0 ≫ φ₁)) := by
    refine (isDerivAt_constVec_iff (c := fun w => e b₀ w ≫ φ₁)).2 fun U hU f => ?_
    refine hw (fun b => fderiv ℂ (fun z => valAt' (e b z ≫ φ₁) U f) 0)
      (differentiableAt_partial (he₁ U f).1 (he₁ U f).2 ⟨⟨hb₀, trivial⟩, hU⟩) ?_
    have hc : ContinuousAt (fun b : V => (b, (0 : Fin g → ℂ))) b₀ := by fun_prop
    have hn := hc.eventually ((he₁ U f).1.mem_nhds ⟨⟨hb₀, trivial⟩, hU⟩)
    refine ((hv U f).differentiableAt (hn.mono fun b hb =>
      ⟨hb.1.1, (le_preimage_dual_iff (hv' b hb.1.1).1 U).2 hb.2⟩)).congr_of_eventuallyEq ?_
    exact hn.mono fun b hb => ((hv' b hb.1.1).2 U hb.2 f).symm
  obtain rfl : u = constVec (e b₀ 0) := H₁.hom_ext ((hu.comp φ₁).unique h3)
    (by rw [h2, Category.assoc, hp b₀ hb₀])
  rwa [Category.assoc, h₀ b₀ hb₀] at h1

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {σ : c.F →+* ℂ} {g : ℕ} {e : Fin g ≃ Letter Dw}

theorem exists_inner_lift (x : CxPts (genStr Z) σ) (hx : Inner x) : ∃ y : Sp ℂ ⟶ Xo.XF c, y ≫ Z.jQ = x.1 := by
  haveI := Z.jQ_open
  refine ⟨IsOpenImmersion.lift Z.jQ x.1 ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact not_not.1 hx

theorem exists_dirs (Fu : Fam Xo c σ e) (a : CxFr Z σ) (y : Sp ℂ ⟶ Xo.XF c) (hy : y ≫ Z.jQ = a.1.1) (i : Fin Fu.n)
    (P : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) (fun j => Formalism.L2.PjFree.relab c σ (e j).1) P)
    (hu : Fu.u i P = y ≫ pullback.fst _ _) :
    ∃ (w : Fin g → Fin g → ℂ) (M : Matrix (Fin g) (Fin g) ℂ), (∀ j, M *ᵥ w j = Pi.single j 1) ∧
      ∀ z : Letter Dw, ∃ v₀ : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left,
        v₀ ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y ∧ v₀ ≫ Z.m.φ = a.2.v z.1 z.2 ∧
        IsDerivAt0 (fun w => (Fu.ex i P w).left) (w (e.symm z)) (v₀ ≫ Z.m0.toSABMap.φ) := by
  have hs : y ≫ pullback.snd _ _ = spMap σ := by
    rw [← Z.jQ_over, ← Category.assoc, hy]; exact a.1.2
  obtain ⟨y', v, hx, hv⟩ := @OpenReg.exists_frPt_of_eigFrame E _ _ _ H Dw l Xo c O _ β Z (CAt σ) inferInstance
    (inferInstanceAs (IsLocalRing ℂ)) inferInstance y hs (a.1.1 ≫ genι Z)
    (by rw [← hy]; exact (Category.assoc _ _ _).symm) a.2
  obtain ⟨w, M, -, hw, hM, -⟩ := AdaptedPeriods.exists_adapted E H Dw l Xo c σ g e Fu y' i P hP (hu.trans hx.symm)
  refine ⟨w, M, hM, fun z => ⟨v z.1 z.2, (hv _ _).1, (hv _ _).2.2, ?_⟩⟩
  have := hw (e.symm z)
  rw [Equiv.apply_symm_apply, ← (hv _ _).2.1] at this
  exact this

theorem exists_hol_per : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (σ : c.F →+* ℂ) (g : ℕ) (e : Fin g ≃ Letter Dw) (Fu : Fam Xo c σ e) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (B : Set V) (a : V → CxFr Z σ), IsOpen B → HolFam B a → (∀ b ∈ B, Inner (a b).1) → ∀ b₀ ∈ B, ∃ (B' : Set V) (i : Fin Fu.n) (Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ))), IsOpen B' ∧ b₀ ∈ B' ∧ B' ⊆ B ∧ (∀ b ∈ B', Per Fu (a b) i (Q b)) ∧ ∀ v z, DifferentiableOn ℂ (fun b => Q b v z) B' := by
  intro E _ _ _ H Dw l Xo c O _ β Z σ g e Fu V _ _ _ B a hB ha hI b₀ hb₀
  haveI := Z.jQ_open
  haveI : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨(exists_inner_lift _ (hI b₀ hb₀)).choose⟩
  choose! y hy using fun b (hb : b ∈ B) => exists_inner_lift _ (hI b hb)
  have hyh : IsHolTo B y := isHolTo_of_comp_open Z.jQ (LocLift.isHolTo_congr ha.1 hy)
  let φ : V ≃L[ℂ] (Fin (Module.finrank ℂ V) → ℂ) := ContinuousLinearEquiv.ofFinrankEq (by simp)
  have hBφ : IsOpen (φ.symm ⁻¹' B) := hB.preimage φ.symm.continuous
  obtain ⟨B₁, i, P₁, hB₁, hb₁, hsub, hP₁, hu₁⟩ := Fu.lift _ (φ.symm ⁻¹' B) (fun t => y (φ.symm t) ≫ pullback.fst _ _) hBφ
    (fun t ht => by
      rw [Category.assoc, pullback.condition, ← Category.assoc, ← Z.jQ_over, ← Category.assoc, hy _ ht,
        ← OpenReg.spMap_comp]
      exact congrArg (· ≫ _) (a _).1.2)
    (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom hyh _) hBφ φ.symm.differentiableOn fun _ h => h) (φ b₀)
    (by simpa using hb₀)
  have hB' : IsOpen (φ ⁻¹' B₁) := hB₁.preimage φ.continuous
  have hsub' : φ ⁻¹' B₁ ⊆ B := fun b hb => by simpa using hsub hb
  have hu : ∀ b ∈ φ ⁻¹' B₁, Fu.u i (P₁ (φ b)) = y b ≫ pullback.fst _ _ := fun b hb => by simpa using hu₁ _ hb
  have hex : IsHolTo ((φ ⁻¹' B₁) ×ˢ Set.univ) fun bz : V × (Fin g → ℂ) => (Fu.ex i (P₁ (φ bz.1)) bz.2).left :=
    LocLift.isHolTo_comp (β := fun bz : V × (Fin g → ℂ) => (φ bz.1, bz.2)) (Fu.hol i _ B₁ P₁ hB₁ hP₁).2
      (hB'.prod isOpen_univ) (by fun_prop) fun _ h => ⟨h.1, trivial⟩
  choose! w M hM hw using fun b (hb : b ∈ φ ⁻¹' B₁) =>
    exists_dirs Fu (a b) (y b) (hy b (hsub' hb)) i (P₁ (φ b)) (hP₁.1 _ hb) (hu b hb)
  have hM' : ∀ b ∈ φ ⁻¹' B₁, M b * (Matrix.of fun i j => w b j i) = 1 := fun b hb => by
    ext i j
    have := congrFun (hM b hb j) i
    rw [Matrix.mul_apply, Matrix.one_apply]
    simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this
  let Q : V → ((Fu.Di i).La →+ (Letter Dw → ℂ)) := fun b =>
    AddMonoidHom.mk' (fun v z => (M b *ᵥ P₁ (φ b) v) (e.symm z)) fun v v' => by
      funext z
      simp [Matrix.mulVec_add]
  refine ⟨φ ⁻¹' B₁, i, Q, hB', hb₁, hsub', fun b hb => ⟨P₁ (φ b), fun z => w b (e.symm z), y b, hP₁.1 _ hb,
    (hu b hb).symm, hy b (hsub' hb), hw b hb, fun v => ?_⟩, fun v z b hb => ?_⟩
  · have h1 := congrArg (· *ᵥ P₁ (φ b) v) (mul_eq_one_comm.1 (hM' b hb))
    simp only [← Matrix.mulVec_mulVec, Matrix.one_mulVec] at h1
    rw [← h1]
    refine Eq.trans ?_ (Equiv.sum_comp e.symm fun j => (M b *ᵥ P₁ (φ b) v) j • w b j).symm
    funext k
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  · have hwd : ∀ j, DifferentiableAt ℂ (fun b => w b j) b := fun j => by
      obtain ⟨z, rfl⟩ := e.symm.surjective j
      refine differentiableAt_dir Z.m0.toSABMap.cart.1 Z.m.cart.1 (LocLift.isHolTo_mono hyh hB' hsub')
        (ex := fun b u => (Fu.ex i (P₁ (φ b)) u).left) hex
        (fun b hb u => (Over.w (Fu.ex i (P₁ (φ b)) u)).trans (hu b hb)) hb (fun u h => ?_)
        (v := fun b => (a b).2.v z.1 z.2) (fun U f => (ha.2 z.1 z.2 U f).mono fun _ h => ⟨hsub' h.1, h.2⟩)
        fun b hb => hw b hb z
      have h0 : IsDerivAt (fun u => (Fu.ex i (P₁ (φ b)) u).left) 0 0 (constVec (Fu.ex i (P₁ (φ b)) 0).left) :=
        (isDerivAt_constVec_iff (c := fun u => (Fu.ex i (P₁ (φ b)) u).left)).2 fun _ _ _ => map_zero _
      exact ((Fu.ex_diff i _ (hP₁.1 _ hb)).2 (Over.homMk _ h.over) h.1).unique ((isDerivAt0_iff _ _ _).2 h)
        ((isDerivAt0_iff _ _ _).2 h0)
    have hMd : ∀ i j, DifferentiableAt ℂ (fun b => M b i j) b :=
      HolFrameMatrix.differentiableAt_of_mul_eq_one M (fun b => Matrix.of fun i j => w b j i) b
        (fun i j => differentiableAt_pi.1 (hwd j) i) (eventually_of_mem (hB'.mem_nhds hb) hM')
    have hPd : DifferentiableAt ℂ (fun b => P₁ (φ b) v) b :=
      ((hP₁.2 v).differentiableAt (hB₁.mem_nhds hb)).comp b φ.differentiableAt
    refine DifferentiableAt.differentiableWithinAt ?_
    show DifferentiableAt ℂ (fun b => ∑ j, M b (e.symm z) j * P₁ (φ b) v j) b
    exact DifferentiableAt.fun_sum fun j _ => (hMd _ j).mul (differentiableAt_pi.1 hPd j)

end GlobalTheory.ShFam.HorLift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSmoothHermitianMetricProjectiveVariety
section
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false
noncomputable section
open Topology Filter
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem exists_partition {F : Type} [Field F] (σ : F →+* ℂ) (X : Var F)
    (W : CxPts X.str σ → Set (CxPts X.str σ)) (hWo : ∀ y, IsOpen (W y)) (hW : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (pt : Fin n → CxPts X.str σ) (χ : Fin n → CxPts X.str σ → ℝ),
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧ (∀ j, tsupport (χ j) ⊆ W (pt j)) ∧
      ∀ j y, CInfAt (χ j) y := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  have hc : ∀ y, ∃ c : AlgChart X.str σ X.dim, y ∈ c.e.source ∧ c.e.source ⊆ W y := fun y => by
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
    exact ⟨c.restr (W y) (hWo y), ⟨hc, hW y⟩, Set.inter_subset_right⟩
  choose c hcy hcW using hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (c y).e.source)
    (fun y => (c y).e.open_source) (fun y _ => Set.mem_iUnion.2 ⟨y, hcy y⟩)
  let pt : Fin t.card → CxPts X.str σ := fun j => (t.equivFin.symm j).1
  let Lc := EuclideanSpace.equiv (Fin X.dim) ℂ
  let L := Lc.toHomeomorph
  let e : Fin t.card → OpenPartialHomeomorph (CxPts X.str σ) (Fin X.dim → ℂ) :=
    fun j => (c (pt j)).e.transHomeomorph L
  have hcov : ∀ y, ∃ j, y ∈ (e j).source := by
    intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    simpa [e, pt] using hy
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := by
    intro i j
    have ho := isOpen_over (c (pt i)).e (c (pt j)).e.open_source
    have hg : ContDiffOn ℂ ∞ ((c (pt j)).e ∘ (c (pt i)).e.symm)
        ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source) :=
      contDiffOn_euclidean.2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho
        (differentiableOn_euclidean.1 ((c (pt i)).holo_trans (c (pt j))) a)
    have h2 := (Lc.contDiff.restrict_scalars ℝ).comp_contDiffOn
      ((hg.restrict_scalars ℝ).comp (Lc.symm.contDiff.restrict_scalars ℝ).contDiffOn
        (s := Lc.symm ⁻¹' ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)) ?_)
    · refine h2.congr_mono ?_ ?_
      · intro v hv
        simp [e, L, Lc]
      · intro v hv
        simpa [e, L, Lc] using hv
    · intro v hv
      simpa using hv
  obtain ⟨χ, h0, h1, hs, hd⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  refine ⟨t.card, pt, χ, h0, h1, fun j => (hs j).trans (hcW (pt j)), fun j y => ?_⟩
  obtain ⟨i, hi⟩ := hcov y
  have hi' : y ∈ (c (pt i)).e.source := hi
  refine cInfAt_of_chart (c (pt i)).e.open_source (c (pt i)) ?_ hi' hi'
  have h3 := (hd j i).comp (Lc.contDiff.restrict_scalars ℝ).contDiffOn
    (s := (c (pt i)).e.target) (fun v hv => by simpa [e, L, Lc] using hv)
  refine h3.congr_mono ?_ Set.inter_subset_left
  intro v hv
  simp [e, L, Lc]

end GlobalTheory.GoodMetric.SmoothMetric

namespace GlobalTheory.GoodMetric.SmoothMetric

theorem cInfAt_sum {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {κ : Type}
    (s : Finset κ) (f : κ → CxPts X.str σ → ℝ) {y : CxPts X.str σ} (h : ∀ j ∈ s, CInfAt (f j) y) :
    CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := X.str) 0 y
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem exists_isMetricOn_top : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  intro F _ σ X ι _ m E
  classical
  choose U A hz hA hU using fun y : CxPts X.str σ => E.loc (under y)
  obtain ⟨n, pt, χ, h0, h1, hs, hd⟩ := exists_partition σ X (fun y => ptsIn X.str σ (U y))
    (fun y => isOpen_ptsIn _) (fun y => mem_ptsIn.2 (hz y))
  let T : Fin n → Mat m X.Fn → CxPts X.str σ → Mat m ℂ := fun j B z => (B * (A (pt j))⁻¹).map (ratVal · z)

  have hpar : ∀ j y, y ∈ tsupport (χ j) → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy B hB =>
    (hU (pt j) (under y) (mem_ptsIn.1 (hs j hy)) B).1 hB
  have hpar' : ∀ j y, χ j y ≠ 0 → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy =>
    hpar j y (subset_tsupport _ hy)
  refine ⟨fun B z τ => ∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ), ⟨?_, ?_, ?_⟩⟩
  · intro y _ B hB τ
    obtain ⟨j, hj⟩ : ∃ j, χ j y ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have := h1 y
      simp [hne] at this
    have hpos : 0 < χ j y := lt_of_le_of_ne (h0 j y) (Ne.symm hj)
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hdet := ((hpar' j y hj B hB).map_of (ratVal · y) ψ hψ).det_ne τ
    have hPD : (((χ j y : ℝ) : ℂ) • (T j B y τ * (T j B y τ)ᴴ)).PosDef :=
      Matrix.PosDef.smul (Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit))) (by exact_mod_cast hpos)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    refine hPD.add_posSemidef (Matrix.posSemidef_sum _ fun i _ => ?_)
    exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.2 (h0 i y))
  · intro y _ B hB τ i k
    have key : ∀ g : ℂ →L[ℝ] ℝ, CInfAt (fun z =>
        g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) y := by
      intro g
      have e : (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) =
          fun z => ∑ j ∈ Finset.univ, χ j z * g ((T j B z τ * (T j B z τ)ᴴ) i k) := by
        funext z
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Matrix.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul, ← Complex.real_smul, map_smul, smul_eq_mul]
      rw [e]
      refine cInfAt_sum _ _ fun j _ => ?_
      by_cases hy : y ∈ tsupport (χ j)
      · have hr (x : Fin (m τ) × Fin (m τ)) : RegAt (under y) ((B * (A (pt j))⁻¹) τ x.1 x.2) :=
          mem_O_ratOf.1 ((hpar j y hy B hB τ).1 _ _)
        have hG : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (m τ) × Fin (m τ) → ℂ => ∑ l, w (i, l) * star (w (k, l)) :=
          ContDiff.sum fun l _ => (contDiff_apply ℝ (fun _ => ℂ) _).mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ (fun _ => ℂ) _))
        refine ((hd j y).comp₂ (cInfAt_ratVal hr (g.contDiff.comp hG))
          (contDiff_fst.mul contDiff_snd)).congr (Eventually.of_forall fun z => ?_)
        simp [T, Matrix.mul_apply, Mat.map]
      · have hz : χ j =ᶠ[𝓝 y] fun _ => 0 := by
          rw [tsupport, ← Set.mem_compl_iff] at hy
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz'
          exact Function.notMem_support.1 fun h => hz' (subset_closure h)
        refine (cInfAt_const (p := X.str) 0 y).congr ?_
        filter_upwards [hz] with z hz'
        simp [hz']
    exact ⟨key Complex.reCLM, key Complex.imCLM⟩
  · intro y _ B hB B' hB' τ
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hBB : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹) := (Fr.mem_iff hB).1 hB'
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : χ j y = 0
    · simp [hj]
    have e := Par.map_mul_of hBB (hpar' j y hj B hB) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    simp only [T]
    rw [e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.GoodMetric.SmoothMetric
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitSectionOfLocalValues
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LocM GlobalTheory.TrueGeo GlobalTheory.Cartier
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FieldPtGlue

section Val
variable {F : Type} [Field F] {X : Scheme.{0}} {x : Sp F ⟶ X}

theorem valF_ne_zero_iff {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a : Γ(X, U)) :
    valF x U a ≠ 0 ↔ ⊤ ≤ x ⁻¹ᵁ X.basicOpen a := by
  have e1 := Scheme.basicOpen_appLE x ⊤ U h a
  rw [top_inf_eq] at e1
  have e2 : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a) = (x.appLE U ⊤ h).hom a := by
    rw [valF, dif_pos h]
    exact (Scheme.ΓSpecIso (CommRingCat.of F)).hom_inv_id_apply _
  have e3 : x ⁻¹ᵁ X.basicOpen a =
      (Sp F).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U a)) := by
    rw [e2]; exact e1.symm
  rw [e3]
  constructor
  · intro hne
    exact (Scheme.basicOpen_of_isUnit _ ((Ne.isUnit hne).map _)).ge
  · intro hle h0
    rw [h0, map_zero, Scheme.basicOpen_zero] at hle
    exact hle (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)

theorem valF_restrict {U V : X.Opens} (e : V ≤ U)
    (h : ⊤ ≤ x ⁻¹ᵁ V) (a : Γ(X, U)) : valF x V ((X.presheaf.map (homOfLE e).op).hom a) = valF x U a := by
  have h' : ⊤ ≤ x ⁻¹ᵁ U := fun q hq => e (h hq)
  rw [valF, valF, dif_pos h, dif_pos h', ← Scheme.Hom.map_appLE x h (homOfLE e).op]
  rfl

theorem valF_sub {U : X.Opens} (h : ⊤ ≤ x ⁻¹ᵁ U) (a b : Γ(X, U)) :
    valF x U (a - b) = valF x U a - valF x U b := by
  simp only [valF, dif_pos h, map_sub]

theorem le_preimage_iff (U : X.Opens) : ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint F) ∈ U := by
  constructor
  · intro h
    exact h (show (IsLocalRing.closedPoint F : Sp F) ∈ (⊤ : (Sp F).Opens) from trivial)
  · intro h y _
    have : y = IsLocalRing.closedPoint F := Subsingleton.elim (α := PrimeSpectrum F) _ _
    subst this
    exact h

end Val

noncomputable def resPt (X : Scheme.{0}) (z : X) : Sp (X.residueField z : Type) ⟶ X := X.fromSpecResidueField z

theorem resPt_le_iff (X : Scheme.{0}) (z : X) (U : X.Opens) : ⊤ ≤ resPt X z ⁻¹ᵁ U ↔ z ∈ U := by
  rw [le_preimage_iff]
  have : resPt X z (IsLocalRing.closedPoint (X.residueField z : Type)) = z :=
    Scheme.fromSpecResidueField_apply z _
  rw [this]

theorem section_ext {X : Scheme.{0}} [IsReduced X] {U : X.Opens} (a b : Γ(X, U))
    (h : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → valF w U a = valF w U b) : a = b := by
  rw [← sub_eq_zero]
  apply eq_zero_of_basicOpen_eq_bot
  rw [eq_bot_iff]
  intro z hz
  have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 (X.basicOpen_le _ hz)
  have h1 := (valF_ne_zero_iff hU (a - b)).2 ((resPt_le_iff X z _).2 hz)
  rw [valF_sub hU, h _ _ hU, sub_self] at h1
  exact absurd rfl h1

theorem exists_unit_of_locally : ∀ (X : Scheme.{0}) [IsReduced X] (U : X.Opens) (P : ∀ (k : Type) [Field k], (Sp k ⟶ X) → k → Prop), (∀ (k : Type) [Field k] (w : Sp k ⟶ X) (a a' : k), ⊤ ≤ w ⁻¹ᵁ U → P k w a → P k w a' → a = a') → (∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → ¬ P k w 0) → (∀ z ∈ U, ∃ (V : X.Opens) (s : Γ(X, V)), z ∈ V ∧ V ≤ U ∧ ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ V → P k w (valF w V s)) → ∃ s : Γ(X, U)ˣ, ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U s.val) := by
  intro X _ U P huniq hne hloc
  choose V s hzV hVU hP using hloc
  let V' : U → X.Opens := fun z => V z.1 z.2
  let s' : ∀ z : U, Γ(X, V' z) := fun z => s z.1 z.2
  have hcov : U ≤ iSup V' := fun z hz =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨⟨z, hz⟩, hzV z hz⟩
  have hcomp : TopCat.Presheaf.IsCompatible X.presheaf V' s' := by
    intro i j
    refine section_ext (X := X) (U := V' i ⊓ V' j) _ _ fun k _ w hw => ?_
    have hi : ⊤ ≤ w ⁻¹ᵁ V' i := fun q hq => (hw hq).1
    have hj : ⊤ ≤ w ⁻¹ᵁ V' j := fun q hq => (hw hq).2
    refine (valF_restrict inf_le_left hw (s' i)).trans
      (Eq.trans ?_ (valF_restrict inf_le_right hw (s' j)).symm)
    exact huniq k w _ _ (fun q hq => hVU i.1 i.2 (hi hq)) (hP i.1 i.2 k w hi) (hP j.1 j.2 k w hj)
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' V' U (fun i => homOfLE (hVU i.1 i.2)) hcov s' hcomp
  have key : ∀ (k : Type) [Field k] (w : Sp k ⟶ X), ⊤ ≤ w ⁻¹ᵁ U → P k w (valF w U t) := by
    intro k _ w hw
    have hz := (le_preimage_iff U).1 hw
    have hV : ⊤ ≤ w ⁻¹ᵁ V _ hz := (le_preimage_iff _).2 (hzV _ hz)
    have e : valF w U t = valF w (V _ hz) (s _ hz) :=
      (valF_restrict (hVU _ hz) hV t).symm.trans (congrArg (valF w (V _ hz)) (ht ⟨_, hz⟩))
    rw [e]
    exact hP _ hz k w hV
  have hu : IsUnit (M := Γ(X, U)) t := by
    apply X.toRingedSpace.isUnit_of_isUnit_germ
    intro z hz
    have hU : ⊤ ≤ resPt X z ⁻¹ᵁ U := (resPt_le_iff X z U).2 hz
    have h0 : valF (resPt X z) U t ≠ 0 := fun h0 => hne _ _ hU (h0 ▸ key _ _ hU)
    have h1 := (resPt_le_iff X z _).1 ((valF_ne_zero_iff hU t).1 h0)
    exact (X.mem_basicOpen t z hz).1 h1
  exact ⟨hu.unit, key⟩

end GlobalTheory.FieldPtGlue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisZero
section
set_option autoImplicit false

noncomputable section

open Topology

namespace GlobalTheory.ShFam.Hor.LogCh

def IsLatBasis {g r : ℕ} (K : Set (Fin g → ℂ)) (b : Fin r → Fin g → ℂ) : Prop :=
  LinearIndependent ℝ b ∧ ∀ w, w ∈ K ↔ ∃ m : Fin r → ℤ, w = ∑ j, m j • b j

def IsLatFam {n g : ℕ} (B : Set (Fin n → ℂ)) (K : (Fin n → ℂ) → Set (Fin g → ℂ)) : Prop :=
  IsOpen B ∧ (∀ b ∈ B, ∃ H : AddSubgroup (Fin g → ℂ), (H : Set (Fin g → ℂ)) = K b) ∧
    IsOpen {q : (Fin n → ℂ) × (Fin g → ℂ) | q.1 ∈ B ∧ q.2 ∉ K q.1} ∧
    ∀ b₀ ∈ B, ∀ w₀ ∈ K b₀, ∃ ζ : (Fin n → ℂ) → Fin g → ℂ, ζ b₀ = w₀ ∧ AnalyticAt ℂ ζ b₀ ∧
      ∀ᶠ q in 𝓝 (b₀, w₀), q.2 ∈ K q.1 ↔ q.2 = ζ q.1

section Exp

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

def IsExpAt (t : SAB H X) (y : Sp ℂ ⟶ X) {g : ℕ} (e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop :=
  (∀ v w, e (v + w) = e v * e w) ∧
    (∀ w, ∃! v, IsTanAtG t y v ∧ IsDerivAt0 (fun u => (e u).left) w v) ∧
    ∀ v, IsTanAtG t y v → ∃! w, IsDerivAt0 (fun u => (e u).left) w v

end Exp

end GlobalTheory.ShFam.Hor.LogCh
end
end

