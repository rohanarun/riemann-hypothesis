module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.AbelianSchemeQuotients.IsAbelianScheme
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0161
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0196
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0183
public import Development.WeilBound.CoreStatements.HomogeneousNonvanishing.LinearIndependentAndExistsTriInLieEigEqSpan
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0078

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbelianSchemeNsmulSurjective
section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace GlobalTheory.CompanionTheory.Ar.Approx

theorem surjective_pow_of_isAbelianScheme :
    ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ n : ℕ, n ≠ 0 →
      Surjective ((𝟙 A) ^ n : A ⟶ A).left := by
  intro K _ A _ hA n hn
  haveI : Smooth A.hom := IsAbelianScheme.smooth (self := hA)
  haveI : IsProper A.hom := IsAbelianScheme.proper (self := hA)
  haveI : GeometricallyConnected A.hom := IsAbelianScheme.geomConnected (self := hA)
  haveI : IsLocallyNoetherian (Sp K) := inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of K)))
  haveI : ConnectedSpace (Sp K) := inferInstanceAs (ConnectedSpace (Spec (CommRingCat.of K)))
  have hw : ((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom = A.hom := Over.w _
  haveI : Flat ((𝟙 A) ^ n : A ⟶ A).left :=
    GlobalTheory.CompanionTheory.Ar.BT.flat_mul_semiAbelian (Sp K) A (GlobalTheory.isSemiAbelian_of_isAbelianScheme A hA) n
      (Nat.one_le_iff_ne_zero.mpr hn)
  haveI : LocallyOfFiniteType ((𝟙 A) ^ n : A ⟶ A).left :=
    HasRingHomProperty.of_comp (fun _ _ h => RingHom.FiniteType.of_comp_finiteType h)
      (by rw [hw]; infer_instance)
  haveI : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
  haveI : LocallyOfFinitePresentation ((𝟙 A) ^ n : A ⟶ A).left := inferInstance
  haveI : UniversallyOpen ((𝟙 A) ^ n : A ⟶ A).left := UniversallyOpen.of_flat _
  haveI : IsProper (((𝟙 A) ^ n : A ⟶ A).left ≫ A.hom) := by rw [hw]; infer_instance
  haveI : IsProper ((𝟙 A) ^ n : A ⟶ A).left := IsProper.of_comp _ A.hom
  haveI : UniversallyOpen A.hom := UniversallyOpen.of_flat _
  haveI : ConnectedSpace A.left := GeometricallyConnected.connectedSpace A.hom A.hom.isOpenMap
  have hclopen : IsClopen (Set.range ((𝟙 A) ^ n : A ⟶ A).left) :=
    ⟨(Scheme.Hom.isClosedMap _).isClosed_range, (Scheme.Hom.isOpenMap _).isOpen_range⟩
  refine ⟨fun y => ?_⟩
  rcases isClopen_iff.mp hclopen with h | h
  · have hy := Set.mem_range_self (f := ⇑((𝟙 A) ^ n : A ⟶ A).left) y
    rw [h] at hy
    exact hy.elim
  · have hy : y ∈ Set.range ⇑((𝟙 A) ^ n : A ⟶ A).left := by rw [h]; trivial
    exact hy

end GlobalTheory.CompanionTheory.Ar.Approx
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginFrameRelayBound
section
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.root_origin_frame_relay_bound : Top.Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (SS : Finset ℕ) (RM : Top.RootModel (CMType H) (Dw.p + Dw.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (Dw.p + Dw.q)) (Option (RootIx Dw))) (Fx : FixedData Y Sys) (Or : RootOrigin Y SS RM Fx) (Fr : Small.GenFrame Or) (A : Subring RM.Ω) (p : ℕ) [Fact p.Prime] (z : (Σ k, RM.ι k) → PadicAlgCl p) (ev : A →+* PadicAlgCl p), z ∈ Small.algPts p (mCoordIdeal RM.y) → (∀ x : A, Small.HasVal RM.y 0 (x : RM.Ω) z (ev x)) → FinRd.GoodRing Fr A → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (y : IntFr Xo c T io) (evT : A →+* T.Fr) (zT : letI := io.toAlgebra; FrPt Xo c T.Fr) (t : Ix Dw → T.Frˣ), FinRd.IsIntPt Fr A ev la T io e y evT zT t → ∀ (zV : Spec (CommRingCat.of T.V) ⟶ Or.𝔐.X), FinRd.Roots.ReadsPt Or.𝔐.ξ A T evT zV → ∀ (EC : Type) [AddCommGroup EC] [Module T.Fr EC] [Module T.V EC] [IsScalarTower T.V T.Fr EC] (MC : LieModel Or.𝔐.t.G (FinRd.Roots.gen T zV) EC) (ρC : 𝓞 E →+* Module.End T.Fr EC), MC.IsActOf Or.𝔐.t.act.act ρC → ∀ (s : CMType H ⊕ CMType H) (u : Fin (labelRk Dw s) → EC) (σ : 𝓞 E →+* T.V), (∀ i, FinRd.Roots.IsFrameVec Or io zT MC (u i) s i) → (∀ a, GlobalTheory.CompanionTheory.Ar.ValAt Or.𝔐.ξ zV (Or.𝔐.emb s a) (σ a)) → LinearIndependent T.Fr u ∧ ∃ yb : Fin (labelRk Dw s) → EC, FinRd.Roots.TriIn u (fun i => (t (Small.labelIx Dw ⟨s, i⟩) : T.Fr)) yb ∧ FinRd.Roots.lieEig Or MC ρC σ = Submodule.span T.V (Set.range yb) := by
  first | exact @PositivityTheory.UnitarySelfGeneration.linearIndependent_and_exists_triIn_lieEig_eq_span | exact PositivityTheory.UnitarySelfGeneration.linearIndependent_and_exists_triIn_lieEig_eq_span
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiAbelianPullbackTorusExtension
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.TopPt

section Alg

variable {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {r : ℕ}

theorem hom_eq_sum {O : Type} [CommRing O] (δ : X →+ O) :
    δ = ∑ i, δ (Module.Free.chooseBasis ℤ X i) •
      (Int.castAddHom O).comp ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
  ext x
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
  simp only [map_zsmul]
  simp [AddMonoidHom.finsetSum_apply, mul_comm]

theorem exists_dual (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) (a : Fin r) :
    ∃ x : X, ∀ φ : X →+ ℤ, φ x = bs.repr φ a := by
  refine ⟨∑ i, bs.repr ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom a • Module.Free.chooseBasis ℤ X i,
    fun φ => ?_⟩
  have e : φ = ∑ i, φ (Module.Free.chooseBasis ℤ X i) •
      ((Module.Free.chooseBasis ℤ X).coord i).toAddMonoidHom := by
    ext x
    set_option synthInstance.maxHeartbeats 100000 in
      conv_lhs => rw [← (Module.Free.chooseBasis ℤ X).sum_repr x, map_sum]
    simp only [map_zsmul]
    simp [AddMonoidHom.finsetSum_apply, mul_comm]
  conv_rhs => rw [e]
  set_option synthInstance.maxHeartbeats 100000 in
    simp [map_sum, mul_comm]

theorem indep {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    LinearIndependent O (fun a => (Int.castAddHom O).comp (bs a)) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg a
  obtain ⟨x, hx⟩ := exists_dual bs a
  have := DFunLike.congr_fun hg x
  simpa [AddMonoidHom.finsetSum_apply, hx, Finsupp.single_apply] using this

theorem span_top {O : Type} [CommRing O] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ)) :
    Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) = ⊤ := by
  have key : ∀ φ : X →+ ℤ, (Int.castAddHom O).comp φ ∈
      Submodule.span O (Set.range fun a => (Int.castAddHom O).comp (bs a)) := by
    intro φ
    have e : (Int.castAddHom O).comp φ = ∑ a, ((bs.repr φ a : ℤ) : O) • (Int.castAddHom O).comp (bs a) := by
      ext x
      have e₀ := DFunLike.congr_fun (bs.sum_repr φ) x
      rw [AddMonoidHom.finsetSum_apply] at e₀
      set_option synthInstance.maxHeartbeats 100000 in
        rw [AddMonoidHom.comp_apply, ← e₀, map_sum]
      simp [AddMonoidHom.finsetSum_apply]
    rw [e]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
  rw [eq_top_iff]
  intro δ _
  rw [hom_eq_sum δ]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (key _)

theorem image_basis {O V : Type} [CommRing O] [AddCommGroup V] [Module O V] (bs : Module.Basis (Fin r) ℤ (X →+ ℤ))
    (io : (X →+ O) →ₗ[O] V) (h : Function.Injective io) :
    LinearIndependent O (fun a => io ((Int.castAddHom O).comp (bs a))) ∧
      LinearMap.range io = Submodule.span O (Set.range fun a => io ((Int.castAddHom O).comp (bs a))) := by
  have hk : LinearMap.ker io = ⊥ := LinearMap.ker_eq_bot_of_injective h
  have hi := (indep (O := O) bs).map' io hk
  refine ⟨hi, ?_⟩
  rw [LinearMap.range_eq_map, ← span_top (O := O) bs, Submodule.map_span, ← Set.range_comp]
  rfl

omit [Module.Free ℤ X] [Module.Finite ℤ X] in
theorem cast_comp {O K : Type} [CommRing O] [CommRing K] (c : O →+* K) (φ : X →+ ℤ) :
    c.toAddMonoidHom.comp ((Int.castAddHom O).comp φ) = (Int.castAddHom K).comp φ := by
  ext x; simp

end Alg

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter _root_.Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

theorem exists_pull {S S' : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (z : S' ⟶ S) :
    ∃ (G₀ : Over S') (_ : GrpObj G₀) (ψ : G₀.left ⟶ G.left), IsSemiAbelian G₀ ∧ IsGrpPullback G₀ G z ψ :=
  ⟨(Over.pullback z).obj G, inferInstance, pullback.fst G.hom z, IsSemiAbelian.pullback z G hG,
    isGrpPullback_pullback G z⟩

theorem lifts_iff {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') {X : Scheme.{0}} {z : Sp R ⟶ X} {G : Over X}
    [GrpObj G] {G₀ : Over (Sp R)} [GrpObj G₀] {ψ : G₀.left ⟶ G.left} (hp : IsGrpPullback G₀ G z ψ)
    {GK : Over (Sp R')} {φ₀ : GK.left ⟶ G₀.left} (hw : φ₀ ≫ G₀.hom = GK.hom ≫ spMap c)
    {V : Type} [AddCommGroup V] [Module R V] (M : LieModel G z V) (M₀ : LieModel G₀ (𝟙 _) V)
    (hM₀ : ∀ e, (M₀.pt e).left ≫ ψ = (M.pt e).left) (e : V) (v : epsAt (𝟙 (Sp R')) ⟶ GK) :
    (v.left ≫ φ₀ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M₀.pt e).left) ↔ (v.left ≫ (φ₀ ≫ ψ) = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap c) ≫ (M.pt e).left) := by
  constructor
  · intro h
    rw [← Category.assoc, h, Category.assoc, hM₀]
  · intro h
    apply hp.1.hom_ext
    · rw [Category.assoc, h, Category.assoc, hM₀]
    · have w₂ := Over.w (M₀.pt e)
      have w₃ := Over.w v
      rw [Category.assoc, hw, ← Category.assoc, w₃, Category.assoc, w₂]
      show (Spec.map _ ≫ 𝟙 _) ≫ Spec.map _ = Spec.map _ ≫ Spec.map _ ≫ 𝟙 _
      rw [Category.comp_id, Category.comp_id, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
        ← CommRingCat.ofHom_comp]
      congr 2
      ext x <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem main : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ X) (GK : Over (Sp L)) [GrpObj GK] (φ : GK.left ⟶ G.left) (τ : TorusExtension GK) (G' : Over (Sp (𝓞 L))) [GrpObj G'] (φ' : τ.B.left ⟶ G'.left), letI := τ.addCommGroup; letI := τ.grpB; IsSemiAbelian G' → IsGrpPullback GK G (spMap (algebraMap (𝓞 L) L) ≫ z) φ → IsGrpPullback τ.B G' (spMap (algebraMap (𝓞 L) L)) φ' → ∀ (MT : LieModel (splitTorus (Sp L) τ.X) (𝟙 _) (τ.X →+ L)), IsCocharLie MT → ∀ (V V' : Type) [AddCommGroup V] [Module (𝓞 L) V] [AddCommGroup V'] [Module (𝓞 L) V'] (M : LieModel G z V) (M' : LieModel G' (𝟙 _) V') (r : ℕ) (bs : Module.Basis (Fin r) ℤ (τ.X →+ ℤ)), ∃ (ε : Fin r → V) (f : V →ₗ[𝓞 L] V'), (∀ a, ((MT.pt ((Int.castAddHom L).comp (bs a)) ≫ τ.i).left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt (ε a)).left)) ∧ (∀ (e : V) (v : epsAt (𝟙 (Sp L)) ⟶ GK), (v.left ≫ φ = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M.pt e).left) → ((v ≫ τ.q).left ≫ φ' = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (GlobalTheory.CompanionTheory.Ar.dualMap (algebraMap (𝓞 L) L)) ≫ (M'.pt (f e)).left)) ∧ LinearIndependent (𝓞 L) ε ∧ LinearMap.ker f = Submodule.span (𝓞 L) (Set.range ε) ∧ ∀ e' : V', ∃ (a : 𝓞 L) (e : V), a ≠ 0 ∧ f e = a • e' := by
  intro X G _ _ hG L _ _ z GK _ φ τ G' _ φ'
  let _ := τ.addCommGroup
  let _ := τ.grpB
  have := τ.free
  have := τ.finite
  intro hG' hφ hφ' MT hMT V V' _ _ _ _ M M' r bs
  obtain ⟨G₀, _, ψ, hG₀, hp⟩ := exists_pull G hG z
  obtain ⟨φO, hF, hw⟩ : ∃ φO : GK.left ⟶ G₀.left, φO ≫ ψ = φ ∧
      φO ≫ G₀.hom = GK.hom ≫ spMap (algebraMap (𝓞 L) L) :=
    ⟨hp.1.lift φ (GK.hom ≫ spMap (algebraMap (𝓞 L) L)) (by rw [hφ.1.w, Category.assoc]), hp.1.lift_fst _ _ _,
      hp.1.lift_snd _ _ _⟩
  subst hF
  have hO : IsGrpPullback GK G₀ (spMap (algebraMap (𝓞 L) L)) φO := hp.cancel hφ hw
  obtain ⟨M₀, hM₀⟩ := (GlobalTheory.CompanionTheory.Ar.LieMove.main (𝓞 L) X z G G₀ ψ V hp).1 M
  have hiff := lifts_iff (algebraMap (𝓞 L) L) hp hw M M₀ hM₀
  obtain ⟨io, f, h1, h2, h3, h4, h5⟩ := GlobalTheory.T.torus_extension_lie_lattice (𝓞 L) L G₀ G' GK τ φO φ'
    hG₀ hG' hO hφ' MT hMT V V' M₀ M'
  obtain ⟨b1, b2⟩ := image_basis bs io h3
  refine ⟨fun a => io ((Int.castAddHom (𝓞 L)).comp (bs a)), f, fun a => ?_, fun e v h => h2 e v ((hiff e v).2 h),
    b1, h4.trans b2, h5⟩
  have := h1 ((Int.castAddHom (𝓞 L)).comp (bs a))
  rw [cast_comp] at this
  exact (hiff _ _).1 this

end GlobalTheory.CompanionTheory.Ar.TopPt
end
end

