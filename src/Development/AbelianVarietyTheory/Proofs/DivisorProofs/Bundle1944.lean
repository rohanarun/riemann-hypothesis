module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1909
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1926
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1895
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1878
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1925
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1899
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1889
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0329
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LawsFieldsSeparately
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1274
public import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1930
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianHaarIndependentOfOrthonormalFrame
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1534
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0119
public import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0508
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1898
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColumnPolynomialLocalDepthEqPlaceDepth
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.PGsh
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1
open GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum GlobalTheory.FactorDepth GlobalTheory.CharDepth GlobalTheory.FGDepth GlobalTheory.PtTie GlobalTheory.PlaceInt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ColDepth

open GlobalTheory.FGDepth

section Ultra

variable {C : Type} [Field C] (v : AddValuation C (WithTop ℝ))

theorem val_eq_of_lt_sub (x y : C) (h : v x < v (x - y)) : v y = v x := by
  have h1 : min (v x) (v (x - y)) ≤ v (x - (x - y)) := AddValuation.map_sub v _ _
  rw [sub_sub_cancel, min_eq_left h.le] at h1
  have h2 : min (v y) (v (x - y)) ≤ v (y + (x - y)) := AddValuation.map_add v _ _
  rw [add_sub_cancel] at h2
  rcases le_total (v y) (v (x - y)) with h3 | h3
  · rw [min_eq_left h3] at h2
    exact le_antisymm h2 h1
  · rw [min_eq_right h3] at h2
    exact absurd (lt_of_le_of_lt h2 h) (lt_irrefl _)

theorem iInf_le_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ t, toE (v (b t)) ≤ ⨅ s, toE (v (a s)) := by
  refine le_iInf fun s => ?_
  by_cases hs : v (a s) = ⊤
  · rw [hs]
    exact le_top
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1 hs
    obtain ⟨N, hN⟩ := exists_nat_gt r
    obtain ⟨t, ht⟩ := h s N
    have hlt : v (a s) < v (a s - b t) :=
      lt_of_lt_of_le (by rw [← hr]; exact WithTop.coe_lt_coe.2 hN) ht
    rw [← val_eq_of_lt_sub v _ _ hlt]
    exact iInf_le _ t

theorem iInf_eq_of_approx {S U : Type} (a : S → C) (b : U → C)
    (h1 : ∀ (s : S) (N : ℕ), ∃ t, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t))
    (h2 : ∀ (t : U) (N : ℕ), ∃ s, ((N : ℝ) : WithTop ℝ) ≤ v (a s - b t)) :
    ⨅ s, toE (v (a s)) = ⨅ t, toE (v (b t)) := by
  refine le_antisymm ?_ (iInf_le_of_approx v a b h1)
  refine iInf_le_of_approx v b a fun t N => ?_
  obtain ⟨s, hs⟩ := h2 t N
  exact ⟨s, by rwa [AddValuation.map_sub_swap]⟩

end Ultra

theorem nuLocOf_eq_nuP : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (p : ℕ) [Fact p.Prime] (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ (y : IntFr Xo c T io) (Ch : IntegralChartA3 Xo c T io y) (cx : Lt1 Dw → ℕ) (n : ℕ) (B : ∀ f : Lt1 Dw, Fin (rk f) → Fin n → T.V), IsCols c T io p cx B → ∀ k : ℕ, nuLocOf Ch (vV T.V (p : T.Fr)).toNat k (polyT B cx) = nuP p y cx := by
  intro E _ _ _ H Dw l Xo c p _ la T io e ho y Ch cx n B hB k
  letI := H.starRing
  obtain ⟨X⟩ := nonempty_valExt_of_overLa la ho
  have hmid : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp Ch X cx B k = GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp Ch X cx := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuLocX_vp GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nuH_vp GlobalTheory.FGDepth.depth
    refine iInf_eq_of_approx (vX_vp X)
      (fun g : {g : PS X.C n (chD Ch.ch) // MvIsInt (vX_vp X) g} => GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.nabX Ch X cx B k g.1)
      (fun f : {f : MvPowerSeries (Σ _ : GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.Col cx, Fin (chD Ch.ch)) X.C // MvIsInt (vX_vp X) f} =>
        derivAt0 (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.polyH X.C cx) (MvPowerSeries.subst (GlobalTheory.IndefiniteRowSideFullHecke.LocalValuationColumns.expH Ch X cx) f.1))
      (fun g N => ?_) (fun f N => ?_)
    · obtain ⟨f, hf, hN⟩ := GlobalTheory.T.exists_integral_germ_on_columns_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k g.1 g.2
      exact ⟨⟨f, hf⟩, hN⟩
    · obtain ⟨g, hg, hN⟩ := GlobalTheory.T.exists_integral_germ_on_copies_same_value E H Dw l Xo c p la T io e ho y Ch X cx n B hB N k f.1 f.2
      exact ⟨⟨g, hg⟩, hN⟩
  exact (GlobalTheory.T.localDepth_over_dvr_eq_over_closed_field E H Dw l Xo c p la T io e ho y Ch X cx n B k).trans
    (hmid.trans (GlobalTheory.T.isotropicFactor_depth_eq_sum_factor_depths E H Dw l Xo c p T io y Ch X cx).1)

end GlobalTheory.ColDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompatibleReductionSystemMapImmersion
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.AbLaw GlobalTheory.FormalAlg

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FormalAlg

theorem isClosedImmersion_subschemeι_comp {R : Type} [CommRing R] {W W' : Scheme.{0}}
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W) [IsSeparated f] [IsImmersion π]
    (T : W'.IdealSheafData) [IsProper (T.subschemeι ≫ π ≫ f)] :
    IsClosedImmersion (T.subschemeι ≫ π) := by
  haveI : IsProper ((T.subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; infer_instance
  haveI : IsProper (T.subschemeι ≫ π) := IsProper.of_comp _ f
  exact IsClosedImmersion.of_isPreimmersion _ (T.subschemeι ≫ π).isClosedMap.isClosed_range

theorem isProper_ker_subschemeι_comp {X Y S : Scheme.{0}} (g : X ⟶ Y) [IsClosedImmersion g]
    (f : Y ⟶ S) [IsProper (g ≫ f)] : IsProper (g.ker.subschemeι ≫ f) := by
  change IsProper (g.imageι ≫ f)
  have hg : g.imageι = inv g.toImage ≫ g := (IsIso.eq_inv_comp _).2 g.toImage_imageι
  rw [hg, Category.assoc]
  infer_instance

theorem mapSystem : ∀ (R : Type) [CommRing R] (I : Ideal R) (W W' : Scheme.{0})
    (f : W ⟶ Spec (CommRingCat.of R)) (π : W' ⟶ W), IsSeparated f → IsImmersion π →
    ∀ t : ℕ → W'.IdealSheafData, IsSystem (π ≫ f) I t → (∀ e, IsProper ((t e).subschemeι ≫ π ≫ f)) →
    IsSystem f I (fun e => (t e).map π) ∧ (∀ e, IsProper (((t e).map π).subschemeι ≫ f)) ∧
      ∀ e, ((t e).map π).comap π = t e := by
  intro R _ I W W' f π hf hπ t ht hp
  have hci : ∀ e, IsClosedImmersion ((t e).subschemeι ≫ π) := fun e =>
    haveI := hp e; isClosedImmersion_subschemeι_comp f π (t e)
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  ·
    show (t e).map π = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1))
    have hle : t (e + 1) ≤ t e := by rw [ht e]; exact le_sup_left
    have hι : IsClosedImmersion (t (e + 1)).subschemeι := inferInstance
    have h1 : ((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι = t e := by
      have := (_root_.GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map _ _ _ hι ⊥ (t e)).1
      rw [bot_sup_eq, Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι,
        sup_eq_right.2 hle] at this
      exact this
    have hbot : (t (e + 1)).comap (t (e + 1)).subschemeι = ⊥ := by
      have := (_root_.GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map _ _ _ hι ⊥ ⊥).2
      rwa [Scheme.IdealSheafData.map_bot, Scheme.IdealSheafData.ker_subschemeι] at this
    have h2 : (t e).comap (t (e + 1)).subschemeι =
        (baseIdeal f (I ^ (e + 1))).comap ((t (e + 1)).subschemeι ≫ π) := by
      conv_lhs => rw [ht e]
      rw [Scheme.IdealSheafData.comap_sup, hbot, bot_sup_eq, _root_.GlobalTheory.FormalAlg.baseIdeal_calculus.1, _root_.GlobalTheory.FormalAlg.baseIdeal_calculus.1,
        Category.assoc]
    have h3 := (_root_.GlobalTheory.ClosedImmIdeal.map_sup_comap_and_comap_map _ _ _ (hci (e + 1)) ⊥ (baseIdeal f (I ^ (e + 1)))).1
    rw [bot_sup_eq, Scheme.IdealSheafData.map_bot] at h3
    calc (t e).map π = (((t e).comap (t (e + 1)).subschemeι).map (t (e + 1)).subschemeι).map π := by
          rw [h1]
      _ = ((t e).comap (t (e + 1)).subschemeι).map ((t (e + 1)).subschemeι ≫ π) := by
          rw [Scheme.IdealSheafData.map_comp]
      _ = ((t (e + 1)).subschemeι ≫ π).ker ⊔ baseIdeal f (I ^ (e + 1)) := by rw [h2, h3]
      _ = (t (e + 1)).map π ⊔ baseIdeal f (I ^ (e + 1)) := rfl
  ·
    haveI := hci e
    haveI : IsProper (((t e).subschemeι ≫ π) ≫ f) := by rw [Category.assoc]; exact hp e
    exact isProper_ker_subschemeι_comp ((t e).subschemeι ≫ π) f
  ·
    haveI := hci e
    refine le_antisymm (Scheme.IdealSheafData.comap_map_le _ _) ?_
    show t e ≤ (((t e).subschemeι ≫ π).ker).comap π
    rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
    have h : pullback.fst π ((t e).subschemeι ≫ π) = pullback.snd _ _ ≫ (t e).subschemeι := by
      rw [← cancel_mono π, pullback.condition, Category.assoc]
    rw [h]
    conv_lhs => rw [← (t e).ker_subschemeι]
    exact Scheme.Hom.le_ker_comp _ _

end GlobalTheory.FormalAlg
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexPointsComponentSamePeriodSpace
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HermitianCompactForm GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.DetLine
open GlobalTheory.CxPts

namespace GlobalTheory.DetLine.SameIndex

theorem exists_lift {X Y : Scheme.{0}} (j : X ⟶ Y) [IsOpenImmersion j] (x : Sp ℂ ⟶ Y)
    (hx : x (IsLocalRing.closedPoint ℂ) ∈ Set.range j) : ∃ y : Sp ℂ ⟶ X, y ≫ j = x := by
  refine ⟨IsOpenImmersion.lift j x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨p, rfl⟩
  obtain rfl : p = IsLocalRing.closedPoint ℂ := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
  exact hx

theorem isHolTo_chart_symm {k : Type} [CommRing k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}
    (c : AlgChart p σ d) {B : Set (ReciprocityTheory.L2DbarEstimates.V d)} (hB : IsOpen B) (h : B ⊆ c.e.target) :
    IsHolTo B fun b => (c.e.symm b).1 := fun U f => by
  refine ⟨?_, (c.holo U f).mono fun b hb => ⟨h hb.1, hb.2⟩⟩
  exact (c.e.continuousOn_symm.mono h).isOpen_inter_preimage hB (isOpen_ptsIn U)

theorem index_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : (Xo.XF c).Opens) (e : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (e.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (P' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : Sp ℂ ⟶ Xo.XF c) (B : GlobalTheory.ProjVar.Var c.F) (io : B.X ⟶ gen Y), IsClosed (U : Set (Xo.XF c)) → IsOpenImmersion io → Set.range io = compactOf Y U → io ≫ genStr Y = B.str → y ≫ toF Xo c = spMap e → y' ≫ toF Xo c = spMap e → Set.range y ⊆ U → Set.range y' ⊆ U → IsPeriod (Fu.Di i) ty P → IsPeriod (Fu.Di i') ty P' → y ≫ toX Xo c = Fu.u i P → y' ≫ toX Xo c = Fu.u i' P' → i = i' := by
  intro E _ _ _ H D l Xo c O _ β Y U e g ty Fu i i' P P' y y' B io _ hio hr hs hy hy' hU hU' hP hP' hu hu'
  classical
  haveI := Y.jQ_open
  let W : B.X.Opens := io ⁻¹ᵁ Y.jQ.opensRange
  haveI : Nonempty (Sp ℂ ⟶ Xo.XF c) := ⟨y⟩
  have hl : ∀ z : CxPts B.str e, z ∈ ptsIn B.str e W → ∃ w : Sp ℂ ⟶ Xo.XF c, w ≫ Y.jQ = z.1 ≫ io :=
    fun z hz => exists_lift Y.jQ _ (mem_ptsIn.1 hz)
  choose! w hw using hl
  have hwσ : ∀ z ∈ ptsIn B.str e W,
      (w z ≫ toX Xo c) ≫ Xo.s = spMap (e.comp (IntermediateField.inclusion c.le).toRingHom) := fun z hz => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ← Y.jQ_over, ← Category.assoc, hw z hz,
      ← OpenReg.spMap_comp, Category.assoc _ io]
    exact congrArg (· ≫ _) ((congrArg (z.1 ≫ ·) hs).trans z.2)
  have hex : ∀ z : CxPts B.str e, ∃ k : Fin Fu.n, z ∈ ptsIn B.str e W →
      ∃ Q, IsPeriod (Fu.Di k) ty Q ∧ Fu.u k Q = w z ≫ toX Xo c := fun z => by
    by_cases hz : z ∈ ptsIn B.str e W
    · obtain ⟨k, Q, h⟩ := Fu.onto _ (hwσ z hz)
      exact ⟨k, fun _ => ⟨Q, h⟩⟩
    · exact ⟨i, fun h => absurd h hz⟩
  choose k hk using hex
  have hcont : ContinuousOn k (ptsIn B.str e W) := by
    intro z₀ hz₀
    obtain ⟨ch, hch⟩ := AlgChart.exists_mem_source (p := B.str) (σ := e) (D := B.dim) z₀
    let T := ch.e.target ∩ ch.e.symm ⁻¹' ptsIn B.str e W
    have hT : IsOpen T := ChartGlue.isOpen_over ch.e (isOpen_ptsIn W)
    have h1 : IsHolTo T fun b => w (ch.e.symm b) :=
      HorLift.isHolTo_of_comp_open Y.jQ (LocLift.isHolTo_congr
        (LocLift.isHolTo_comp_hom (isHolTo_chart_symm ch hT Set.inter_subset_left) io) fun b hb => hw _ hb.2)
    let φ : ReciprocityTheory.L2DbarEstimates.V B.dim ≃L[ℂ] (Fin B.dim → ℂ) := EuclideanSpace.equiv (Fin B.dim) ℂ
    have hTφ : IsOpen (φ.symm ⁻¹' T) := hT.preimage φ.symm.continuous
    obtain ⟨B₁, k₀, Q, hB₁, hb₁, hsub, hQ, hQu⟩ := Fu.lift _ (φ.symm ⁻¹' T)
      (fun t => w (ch.e.symm (φ.symm t)) ≫ toX Xo c) hTφ (fun t ht => hwσ _ ht.2)
      (LocLift.isHolTo_comp (LocLift.isHolTo_comp_hom h1 _) hTφ φ.symm.differentiableOn fun _ h => h)
      (φ (ch.e z₀)) (by
        rw [Set.mem_preimage, φ.symm_apply_apply]
        exact ChartGlue.mem_over ch.e hch hz₀)
    have hc : ContinuousAt (fun z => φ (ch.e z)) z₀ := φ.continuous.continuousAt.comp (ch.e.continuousAt hch)
    have hev : k =ᶠ[nhds z₀] fun _ => k₀ := by
      filter_upwards [hc.eventually (hB₁.mem_nhds hb₁), ch.e.open_source.mem_nhds hch,
        (isOpen_ptsIn W).mem_nhds hz₀] with z h₁ h₂ h₃
      obtain ⟨Q', hQ', hQu'⟩ := hk z h₃
      refine Fu.disj _ _ Q' (Q _) hQ' (hQ.1 _ h₁) (hQu'.trans ?_)
      rw [hQu _ h₁, φ.symm_apply_apply, ch.e.left_inv h₂]
    exact (continuousAt_const.congr hev.symm).continuousWithinAt
  have hpt : ∀ (j : Fin Fu.n) (R : (Fu.Di j).La →+ (Fin g → ℂ)) (x : Sp ℂ ⟶ Xo.XF c), x ≫ toF Xo c = spMap e →
      Set.range x ⊆ U → IsPeriod (Fu.Di j) ty R → x ≫ toX Xo c = Fu.u j R → ∃ z ∈ ptsIn B.str e W, k z = j := by
    intro j R x hx hxU hR hxu
    obtain ⟨z, hz⟩ := exists_lift io (x ≫ Y.jQ) (by
      rw [hr]
      exact subset_closure ⟨_, hxU ⟨_, rfl⟩, rfl⟩)
    have hze : z ≫ B.str = spMap e := by
      rw [← hs, ← Category.assoc, hz, Category.assoc]
      exact (congrArg (x ≫ ·) Y.jQ_over).trans hx
    have hzW : (⟨z, hze⟩ : CxPts B.str e) ∈ ptsIn B.str e W :=
      mem_ptsIn.2 ⟨x (IsLocalRing.closedPoint ℂ), (congrArg (fun f => f (IsLocalRing.closedPoint ℂ)) hz).symm⟩
    refine ⟨_, hzW, ?_⟩
    obtain ⟨Q', hQ', hQu'⟩ := hk _ hzW
    have hwx : w ⟨z, hze⟩ = x := (cancel_mono Y.jQ).1 ((hw _ hzW).trans hz)
    exact Fu.disj _ _ Q' R hQ' hR (hQu'.trans (by rw [hwx, hxu]))
  obtain ⟨z, hz, rfl⟩ := hpt i P y hy hU hP hu
  obtain ⟨z', hz', rfl⟩ := hpt i' P' y' hy' hU' hP' hu'
  exact (_root_.GlobalTheory.CxConn.isPreconnected_ptsIn c.F B e W).constant hcont hz hz'

end GlobalTheory.DetLine.SameIndex
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionality
section
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.DegCmp GlobalTheory.DegVal GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open scoped ENNReal NNReal

theorem GlobalTheory.DegVal.compDeg_between : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r), UnfAll U → Proport U → EqVolume U → ∀ u : GlobalTheory.AllWt.Weight Dw, (∀ τ, StrictAnti (u τ)) → (∀ τ, StrictAnti (uPrime Dw u τ)) → (∀ Z, BirOn U Z (wtOf Dw u 0)) → (∀ Z, ValMult U Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0)) → ∀ Z Z' : Comp Xo c, delPrime U Z' u ≤ compDeg U Z (wtOf Dw u 0) ∧ (compDeg U Z (wtOf Dw u 0) : ℝ) ≤ delPrime U Z' u / (1 - rhoB Dw u) := by
  intro E _ _ _ H Dw l Xo c r U hU hP hV u hu hu' hB hM Z Z'
  have h1 : 0 < 1 - rhoB Dw u := sub_pos.2 (rhoOf_lt_one hu' hu)
  have h2 : ∀ la, topDeg U Z' la = topDeg U Z la := fun la => by rw [topDeg, topDeg, hV Z' Z]
  constructor
  · rw [delPrime, h2]
    have hlow := _root_.GlobalTheory.DegVal.growthOn_le_compDeg E H Dw l Xo c r U hU Z (wtOf Dw u 0) (wtOf Dw (uPrime Dw u) 0) (even_wtOf u 0)
      (even_wtOf _ 0) (by rw [hP Z u hu]; exact ENNReal.ofReal_ne_top) (hB Z) (hM Z)
    rw [hP Z _ hu', ← ENNReal.ofReal_natCast] at hlow
    exact (ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).1 hlow
  · rw [delPrime_eq U Z' (vdm_pos hu).ne', mul_div_cancel_left₀ _ h1.ne', h2]
    exact GlobalTheory.DegTop.compDeg_le hP Z hu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstLengthFlatSectionEqFrameNormComplexEmbeddin
section
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

noncomputable section

namespace GlobalTheory.PtDegArch

theorem good_case (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) (hL : Laws U x) (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K) (hy : LiesOn Z y) (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)) (hh : F.IsHerm h) (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K) (hu : GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u) (hu' : GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u') (σ : K →+* ℂ) (hσ : GoodEmb c (σ.comp (algebraMap c.F K))) :
    s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  set σ₀ := σ.comp (algebraMap c.F K) with hσ₀
  let φ : K →ₐ[c.F] CAt σ₀ := { σ with commutes' := fun a => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo c K (CAt σ₀) φ y
  obtain ⟨k, w, t, ho, hb⟩ := GlobalTheory.LamT.exists_ortho_frBor E H Dw l Xo c σ₀ r (U σ₀) (hL.unf σ₀ hσ) z
  have hon : (⟨k, w.1⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z :=
    ⟨w.2, liesOn_frBor hb (liesOn_frMap hz hy)⟩
  have hgood : goodOf c σ₀ = σ₀ := if_pos hσ
  have hinf := s.norm_inf σ₀
  rw [hgood] at hinf
  have h1 : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ = s.cInf σ₀ := by
    have : homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig ⟨k, w.1⟩ ∈
        homN (U σ₀) x (wtOf Dw (flatWt Dw τ) 0) s.sig '' framesOn (U σ₀) Z := ⟨_, hon, rfl⟩
    rw [hinf] at this
    exact this
  rw [GlobalTheory.CompHS.homN_eq_homFac] at h1
  have h2 := GlobalTheory.evR_frBor_of_mem_secZ GlobalTheory.lawsFieldsSeparately.2.1 Xo c _ s.sig_mem (CAt σ₀) t _ _ hb
  have h3 := GlobalTheory.FrameEval.evR_frMap_of_isReduced E H Dw l Xo c s.sig s.sig_mem.1 φ y z hz
  have h4 := _root_.GlobalTheory.PtDegOrtho.homFac_eq_gram_ortho E H Dw l Xo c r U x hL τ K y B t₀ m1 m2 F h hh u u' hu hu' σ hσ φ (fun _ => rfl) z hz k w t ho hb
  rw [← h1, h4]
  have h5 : ‖σ (evR Xo c s.sig y)‖ = ‖GlobalTheory.CompHS.diagChar (exOf Dw (flatWt Dw τ) 0) t‖ * ‖toC (evR Xo c s.sig ((U σ₀).un k w))‖ := by
    rw [← norm_mul]
    show ‖toC (φ (evR Xo c s.sig y))‖ = _
    rw [← h3, h2]
    rfl
  rw [h5]
  ring

theorem cInf_eq_frame_norm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c) (τ : Psi H) (s : ArchSec U x Z (flatWt Dw τ)) (K : Type) [Field K] [NumberField K] [Algebra c.F K] (y : FrPt Xo c K), LiesOn Z y → ∀ (B : GlobalTheory.CM.PAT H (Sp (𝓞 K))) (t₀ : SAB H (Sp K)) (m1 : SABMap t₀ Xo.univ.t y.x) (m2 : SABMap t₀ B.t (spMap (algebraMap (𝓞 K) K))) (F : GlobalTheory.CM.GenFib B.pol) (h : ReciprocityTheory.GeometryOfNumbersTheory.HermFam K (Fin F.P₀.g → K)), F.IsHerm h → ∀ (u : Fin (Dw.mult τ.1) → Fin F.P₀.g → K) (u' : Fin (Dw.mult (conjEmb τ.1)) → Fin F.P₀.g → K), GlobalTheory.PtDeg.FrameCoord y m1 m2 F τ.1 u → GlobalTheory.PtDeg.FrameCoord y m1 m2 F (conjEmb τ.1) u' → ∀ σ : K →+* ℂ, s.cInf (σ.comp (algebraMap c.F K)) = ‖σ (evR Xo c s.sig y)‖ * Real.sqrt (h.gram σ u).det.re / Real.sqrt (h.gram σ u').det.re := by
  intro E _ _ _ H Dw l Xo c r U x hL Z τ s K _ _ _ y hy B t₀ m1 m2 F h hh u u' hu hu' σ
  by_cases hσ : GoodEmb c (σ.comp (algebraMap c.F K))
  · exact good_case E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu' σ hσ
  · set σ' := (starRingEnd ℂ).comp σ
    have e0 : σ'.comp (algebraMap c.F K) = (starRingEnd ℂ).comp (σ.comp (algebraMap c.F K)) := RingHom.comp_assoc _ _ _
    have hσ' : GoodEmb c (σ'.comp (algebraMap c.F K)) := by
      have := goodEmb_goodOf c (σ.comp (algebraMap c.F K))
      rw [goodOf, if_neg hσ] at this
      rw [e0]; exact this
    have hg := good_case E H Dw l Xo c r U x hL Z τ s K y hy B t₀ m1 m2 F h hh u u' hu hu' σ' hσ'
    have hc : s.cInf (σ'.comp (algebraMap c.F K)) = s.cInf (σ.comp (algebraMap c.F K)) := by
      have i1 := s.norm_inf (σ.comp (algebraMap c.F K))
      have i2 := s.norm_inf (σ'.comp (algebraMap c.F K))
      rw [e0, goodOf_conj, i1] at i2
      exact (Set.singleton_eq_singleton_iff.1 i2).symm
    have hgr : ∀ {n : ℕ} (v : Fin n → Fin F.P₀.g → K), (h.gram σ' v).det.re = (h.gram σ v).det.re := fun v => by
      have : h.gram σ' v = (h.gram σ v).map (starRingEnd ℂ) := by
        ext i j
        simp only [ReciprocityTheory.GeometryOfNumbersTheory.HermFam.gram, Matrix.of_apply, Matrix.map_apply]
        exact _root_.GlobalTheory.CM.LieMetricConj.form_conj K B.pol F h hh σ (v i) (v j)
      rw [this]
      change ((starRingEnd ℂ).mapMatrix (h.gram σ v)).det.re = _
      rw [← RingHom.map_det, Complex.conj_re]
    rw [← hc, hg, hgr, hgr]
    simp only [σ', RingHom.comp_apply, Complex.norm_conj]

end GlobalTheory.PtDegArch
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CountableRationalSubgroupInRealSpecialUnitary
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.CovTop.VolUp
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.StandardLattice Formalism.IndefR.Lev Formalism.IndefR.Datum GlobalTheory.AdelicScalar
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CovTop.VolUp

theorem countable_inReal_of_numberField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)), Countable (inReal Ψ G Γ) := by
  intro E _ _ _ r Ψ G Γ
  haveI : Countable E := (Module.finBasis ℚ E).equivFun.injective.countable
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Units.val_injective.countable
  have h : ((Γ.map (embGL Ψ r) : Subgroup (Ψ → GL (Fin r) ℂ)) : Set (Ψ → GL (Fin r) ℂ)).Countable := by
    rw [Subgroup.coe_map]
    exact (Set.to_countable _).image _
  haveI : Countable (Γ.map (embGL Ψ r)) := h.to_subtype
  refine Function.Injective.countable
    (f := fun x : inReal Ψ G Γ => (⟨x.1.1, x.2⟩ : Γ.map (embGL Ψ r))) ?_
  intro x y hxy
  have h2 : x.1.1 = y.1.1 := Subtype.mk.inj hxy
  exact Subtype.ext (Subtype.ext h2)

end GlobalTheory.CovTop.VolUp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverFunctionFieldMapEq
section
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ArInt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

namespace GlobalTheory.Mean4O.Cover

theorem φ_eq_fnMap {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) :
    ∃ hη : V.π (genericPoint V.G) ⤳ genericPoint Y.X, V.φ = GlobalTheory.TrueGeo.SmallSec.fnMap V.π hη := by
  have e : V.π (genericPoint V.G) = genericPoint Y.X := by
    have hc : (spMap V.φ) (IsLocalRing.closedPoint (V.G.presheaf.stalk (genericPoint V.G))) =
        IsLocalRing.closedPoint (Y.X.presheaf.stalk (genericPoint Y.X)) :=
      Subsingleton.elim (α := PrimeSpectrum (Y.X.presheaf.stalk (genericPoint Y.X))) _ _
    refine (congrArg V.π Scheme.fromSpecStalk_closedPoint.symm).trans ?_
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans ?_
    refine (congrArg (fun f => f (IsLocalRing.closedPoint (V.G.presheaf.stalk (genericPoint V.G)))) V.φ_spec).trans ?_
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    rw [hc]
    exact Scheme.fromSpecStalk_closedPoint
  refine ⟨specializes_of_eq e, ?_⟩
  have key : Spec.map (CommRingCat.ofHom V.φ) =
      Spec.map (Y.X.presheaf.stalkSpecializes (specializes_of_eq e) ≫ V.π.stalkMap (genericPoint V.G)) := by
    rw [← cancel_mono (Y.X.fromSpecStalk (genericPoint Y.X)), Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.SpecMap_stalkMap_fromSpecStalk]
    exact V.φ_spec.symm
  exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)

end GlobalTheory.Mean4O.Cover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubeValueConstPointsTangentEqDualFibreValueStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubeValue_constPoints_tangent_eq_dualFibreValue : ∀ {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} [Algebra (FractionRing R) ℂ] {N : NumD ℂ} {g : ℕ}
    (ν : NumOf D ℂ N) (d : AB N.toNumB g) (gm : GtPt D (TE R ℂ)),
    (∃ o : GtPtF D ℂ, o.IsZero ∧ GtPt.IsPullF ℂ (redE ℂ) gm o) →
    ∀ (χ χ' : D.X) (x y : Fin g → ℂ),
    ν.eA (d.ex x) = DegPre.cF D ℂ χ → ν.eA (d.ex y) = DegPre.cF D ℂ χ' →
    ∃ (U : (DegPre.BF D ℂ).left.Opens) (f : Γ((DegPre.BF D ℂ).left, U)),
      vE (DegPre.cubAtT D (TE R ℂ) (DegPre.cT D (TE R ℂ) χ) (DegPre.cT D (TE R ℂ) χ') gm.b) (𝟙 _) ν.J =
        valR (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) gm.b).left U f ∧
      ⊤ ≤ ptB ν d 0 ⁻¹ᵁ U ∧
      ∀ z, ⊤ ≤ ptB ν d z ⁻¹ᵁ U →
        (∀ I : thK.{0}, ⊤ ≤ (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, z] i))).left ⁻¹ᵁ
          D.P.L.U (ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)) ∧
        valF (ptB ν d z) U f =
          valF (lift (ν.eA (d.ex x)) (lift (ν.eA (d.ex y)) (ν.eA (d.ex z)))).left
            (LB.wchart D.P.L (thφ D.P.A (x3 D.P.A)) (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left))
            (D.cub.t.s (fun I : thK.{0} => ν.J (ν.eA (d.ex (∑ i ∈ I.down, ![x, y, 0] i))).left)).val := by
  first | exact @GlobalTheory.MBLow.JetGeo.jet_geo | exact GlobalTheory.MBLow.JetGeo.jet_geo | (intros; apply GlobalTheory.MBLow.JetGeo.jet_geo <;> assumption)
end

