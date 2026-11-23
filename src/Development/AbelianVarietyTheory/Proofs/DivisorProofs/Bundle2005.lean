module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1902
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1954
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CocycleTrivialOnProjectiveCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1885
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1890
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1891
public import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1907
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1894
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0162
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0110
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.SiegelPullbackTransfer.AdelicGL2ExtOfLocalComponents
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRefinementOfIsLimit
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1942
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaPointShapePrimitivityNearGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CharZeroOfIsPrimitiveRoot
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1965
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1948
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1968
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1966
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1943
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenLocusTorsionSectionsHeckeKernel
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0141
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticChange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1979
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbundleFrameAffineAtlas
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace _root_.CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

theorem valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    (f : Γ(X, V)) : valF w V f = ev w V hV f :=
  GlobalTheory.Points.valR_eq w V hV f

theorem map_valF_eq_ev {K : Type} [Field K] {X : Scheme.{0}} (w : Sp K ⟶ X) (V : X.Opens) (hV : ⊤ ≤ w ⁻¹ᵁ V)
    {m n : Type} (A : Matrix m n Γ(X, V)) : A.map (valF w V) = A.map (ev w V hV) := by
  ext i j
  exact valF_eq_ev w V hV _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {Y : Model Xo c (RingHom.id c.F)} {p : Proj (RingHom.id c.F)}

def trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) : Matrix (Fin (N + 1)) (Fin k.M.n) Γ(Y.X, k.V) :=
  (A₀.map (resG Y.X hV)).submatrix id (finCongr (congrArg (fun M : GChart Y => M.n) hk))

def trC {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U)) : Matrix (Fin k.M.n) (Fin (N + 1)) Γ(Y.X, k.V) :=
  (C₀.map (resG Y.X hV)).submatrix (finCongr (congrArg (fun M : GChart Y => M.n) hk)) id

theorem trC_mul_trA {k : ECh Y p} {M₀ : GChart Y} (hk : k.M = M₀) {U : Y.X.Opens} (hV : k.V ≤ U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (C₀ : Matrix (Fin M₀.n) (Fin (N + 1)) Γ(Y.X, U))
    (h : C₀ * A₀ = 1) : trC hk hV C₀ * trA hk hV A₀ = 1 := by
  subst hk
  ext i j
  have := congrArg (fun A => resG Y.X hV (A i j)) h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Matrix.mul_apply, map_sum, map_mul] at this
  simp only [trC, trA, Matrix.mul_apply, Matrix.submatrix_apply, Matrix.map_apply, finCongr_apply, Fin.cast_eq_self, id]
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tw_tr [IsReduced Y.X] {k k' : ECh Y p} {M₀ M₀' : GChart Y} (hk : k.M = M₀) (hk' : k'.M = M₀')
    {U U' : Y.X.Opens} (hV : k.V ≤ U) (hV' : k'.V ≤ U') (hUM : U ⊓ U' ≤ M₀'.U ⊓ M₀.U) {N : ℕ}
    (A₀ : Matrix (Fin (N + 1)) (Fin M₀.n) Γ(Y.X, U)) (A₀' : Matrix (Fin (N + 1)) (Fin M₀'.n) Γ(Y.X, U'))
    (g : Γ(Y.X, U ⊓ U')ˣ)
    (H : ∀ (K : Type) [Field K] (w : Sp K ⟶ Y.X), ⊤ ≤ w ⁻¹ᵁ U → ⊤ ≤ w ⁻¹ᵁ U' →
      A₀.map (valF w _) = valF w _ g.val • (A₀'.map (valF w _) * (chg M₀'.toMChart M₀.toMChart).map (valF w _)))
    (S : Type) [CommRing S] (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ k.V) (h' : ⊤ ≤ x ⁻¹ᵁ k'.V)
    (hM : ⊤ ≤ x ⁻¹ᵁ (k'.M.U ⊓ k.M.U)) :
    ∃ a : Sˣ, (trA hk hV A₀).map (ev x _ h) =
      (a : S) • ((trA hk' hV' A₀').map (ev x _ h') * (chg k'.M.toMChart k.M.toMChart).map (ev x _ hM)) := by
  subst hk hk'
  have key : ∀ r j, resG Y.X (inf_le_left : U ⊓ U' ≤ U) (A₀ r j) =
      g.val * ∑ t, resG Y.X inf_le_right (A₀' r t) * resG Y.X hUM (chg k'.M.toMChart k.M.toMChart t j) := by
    intro r j
    refine GlobalTheory.TwistEmb.eq_of_valR fun K _ w hw => ?_
    have hw1 := le_preimage_mono inf_le_left hw
    have hw2 := le_preimage_mono inf_le_right hw
    have hw3 := le_preimage_mono hUM hw
    have e := congrFun (congrFun (H K w hw1 hw2) r) j
    simp only [Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, smul_eq_mul, valF_eq_ev w U hw1,
      valF_eq_ev w U' hw2, valF_eq_ev w _ hw, valF_eq_ev w _ hw3] at e
    show valF w _ _ = valF w _ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [valF_eq_ev w _ hw, valF_eq_ev w _ hw, ev_res w _ hw hw1, e, map_mul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [map_mul, ev_res w _ hw hw2, ev_res w _ hw hw3]
  have hx : ⊤ ≤ x ⁻¹ᵁ (U ⊓ U') := GlobalTheory.TwistEmb.le_inf' x (le_preimage_mono hV h) (le_preimage_mono hV' h')
  refine ⟨Units.map (ev x _ hx).toMonoidHom g, ?_⟩
  ext r j
  simp only [trA, Matrix.map_apply, Matrix.smul_apply, Matrix.mul_apply, Matrix.submatrix_apply, finCongr_apply,
    Fin.cast_eq_self, id, smul_eq_mul, Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [ev_res x hV h (le_preimage_mono hV h), ← ev_res x inf_le_left hx (le_preimage_mono hV h), key, map_mul,
    map_sum]
  congr 1
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [map_mul, ev_res x inf_le_right hx (le_preimage_mono hV' h'), ev_res x hV' h' (le_preimage_mono hV' h'),
    ev_res x hUM hx hM]

theorem exists_atlas : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H)
    (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)),
    PushInvertible Y.t.G Y.t.PP.L → Nonempty (Atlas Y p) := by
  intro E _ _ _ H Dw l Xo c Y p hP
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => exists_gChart hP x)
    (fun K _ w j hw => by
      have hh : ⊤ ≤ w ⁻¹ᵁ (j.U ⊓ j.U) := GlobalTheory.TwistEmb.le_inf' w hw hw
      show (chg j.toMChart j.toMChart).map (valF w (j.U ⊓ j.U)) = 1
      rw [map_valF_eq_ev w _ hh, chg_map _ _ w hw hw hh, Module.Basis.toMatrix_self])
    (fun K _ w j j' j'' h1 h2 h3 => by
      show (chg j.toMChart j'.toMChart).map (valF w (j.U ⊓ j'.U)) *
        (chg j'.toMChart j''.toMChart).map (valF w (j'.U ⊓ j''.U)) =
        (chg j.toMChart j''.toMChart).map (valF w (j.U ⊓ j''.U))
      rw [map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h2), map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h2 h3),
        map_valF_eq_ev w _ (GlobalTheory.TwistEmb.le_inf' w h1 h3), chg_map _ _ w h1 h2, chg_map _ _ w h2 h3,
        chg_map _ _ w h1 h3, Module.Basis.toMatrix_mul_toMatrix])
  have hcovL : ∀ x : Y.X, ∃ i, x ∈ L.U i := fun x => exists_chart L.isLB x
  have hk : ∀ x : Y.X, ∃ i, ∃ k : ECh Y p, k.M = σ i ∧ x ∈ k.V ∧ IsAffineOpen k.V ∧ k.V ≤ L.U i := fun x => by
    obtain ⟨i, hi⟩ := hcovL x
    obtain ⟨k, h1, h2, h3, h4⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_eCh_le E H Dw l Xo c Y p (σ i) x (hle i hi) (L.U i) hi
    exact ⟨i, k, h1, h2, h3, h4⟩
  choose ix kx hkM hxk haffk hlek using hk
  have hc : IsCompact (Set.univ : Set Y.X) := by
    have e : (Set.univ : Set Y.X) = ⋃ i, ((L.U i : Y.X.Opens) : Set Y.X) :=
      (Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 (hcovL x)).symm
    rw [e]
    exact isCompact_iUnion fun i => (haff i).isCompact
  obtain ⟨t, ht⟩ := hc.elim_finite_subcover (fun x => ((kx x).V : Set Y.X)) (fun x => (kx x).V.isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxk x⟩)
  have hUM : ∀ i i', L.U i ⊓ L.U i' ≤ (σ i').U ⊓ (σ i).U := fun i i' =>
    le_inf (inf_le_right.trans (hle i')) (inf_le_left.trans (hle i))
  exact ⟨{
    B := t
    fin := inferInstance
    k := fun b => kx b.1
    aff := fun b => haffk b.1
    cov := fun x => by
      obtain ⟨z, hz, hxz⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
      exact ⟨⟨z, hz⟩, hxz⟩
    N := N
    A := fun b => trA (hkM b.1) (hlek b.1) (A (ix b.1))
    C := fun b => trC (hkM b.1) (hlek b.1) (C (ix b.1))
    CA := fun b => trC_mul_trA _ _ _ _ (hCA _)
    tw := fun S _ x b b' h h' hM => tw_tr (hkM b.1) (hkM b'.1) (hlek b.1) (hlek b'.1) (hUM _ _) (A (ix b.1))
      (A (ix b'.1)) (L.g (ix b.1) (ix b'.1)) (fun K _ w hw hw' => htw K w _ _ hw hw') S x h h' hM }⟩

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionTruncatedFrameChartResidueCharZer
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
open IsLocalRing Formalism.MainNotions.ModuliIntegralCharts.H1 ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExtScaleZero


set_option maxHeartbeats 1000000 in
theorem exists_ext_all_models_uniformised_charZero (E : Type) [Field E] [NumberField E] [IsCMField E]
    (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l)
    (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (h0 : CharZero (ResidueField T.V)) :
    ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (e' : ℕ), CharZero (ResidueField T'.V) ∧ 0 < e' ∧
      (∀ I : IntData Xo c T' io' y'.1, ∃ P : PELUnif (maximalIdeal T'.V) I.G, P.TorsionIso) ∧
      letI := io.toAlgebra; letI := io'.toAlgebra; ∃ φ : T.Fr →ₐ[c.F] T'.Fr,
        (∀ a : T.Fr, a ≠ 0 → vV T'.V (φ a) = (e' : ℤ) * vV T.V a) ∧ FrMap φ y.1 y'.1 := by
  obtain ⟨G, t, m1, m2, -⟩ := y.2.2
  obtain ⟨W, _, _, _, hc, _, hf, hi, hS⟩ := GlobalTheory.UnifTrait.exists_split_baseChange T.V G.G G.semi
  have hz : CharZero W := charZero_of_injective_ringHom hi
  let T' : Formalism.L2.Pj.CDVR := { V := W }
  have : FaithfulSMul T.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hfin : (algebraMap T.V W).Finite := RingHom.finite_algebraMap.2 hf
  have hl : IsLocalHom (algebraMap T.V W) := hfin.to_isIntegral.isLocalHom hi
  have hres : CharZero (ResidueField W) :=
    charZero_of_injective_ringHom (ResidueField.map (algebraMap T.V W)).injective
  have hj : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T.V W)) :=
    (IsFractionRing.injective W _).comp hi
  obtain ⟨φ, hφ⟩ : ∃ φ : T.Fr →+* T'.Fr, ∀ v, φ (algebraMap T.V T.Fr v) = algebraMap T'.V T'.Fr (algebraMap T.V W v) :=
    ⟨IsFractionRing.lift hj, IsFractionRing.lift_algebraMap hj⟩
  obtain ⟨r, hr0, hv⟩ := GlobalTheory.IntegralPull.exists_index (V' := T'.V) (algebraMap T.V W) φ hφ
  letI := io.toAlgebra
  letI := (φ.comp io).toAlgebra
  let ψ : T.Fr →ₐ[c.F] T'.Fr := { φ with commutes' := fun _ => rfl }
  obtain ⟨z, hz⟩ := GlobalTheory.FramedBaseChange.exists_frMap GlobalTheory.firstFiveLaws.1 E H Dw l Xo c _ _ ψ y.1
  obtain ⟨p, χ, y₀, hy₀⟩ := y.2.1
  let y' : IntFr Xo c T' (φ.comp io) :=
    ⟨z, ⟨p, ψ.comp χ, y₀, Formalism.L2.Pj.frMap_trans (Xo := Xo) (c := c) _ _ _ χ ψ y₀ y.1 z hy₀ hz⟩,
      GlobalTheory.IntegralPull.integral_baseChange T T' io (φ.comp io) _ hi ψ hφ y.1 z hz y.2.2⟩
  exact ⟨T', φ.comp io, y', r, hres, hr0,
    fun I => GlobalTheory.IntegralPull.exists_unif_of_split T T' _ φ hφ m1 m2 hz.1 I.m1 I.m2 hS, ψ, fun a _ => hv a, hz⟩

end GlobalTheory.ExtScaleZero

namespace GlobalTheory.ExtScaleZero


set_option maxHeartbeats 1000000 in
theorem exists_ext_chart_scale_charZero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), letI := H.starRing; ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), CharZero (ResidueField T.V) → ∀ φ : ℝ, GlobalTheory.SlopeRec.HasPhi y φ → ∃ (T' : CDVR) (io' : c.F →+* T'.Fr) (y' : IntFr Xo c T' io') (r : ℕ) (C : IntegralChartA3 Xo c T' io' y') (P : PELUnif (maximalIdeal T'.V) C.I.G), CharZero (ResidueField T'.V) ∧ 0 < r ∧ FrTrunc C.I.G (𝟙 (Sp T'.V)) (chD C.ch) C.xT C.eT ∧ P.TorsionIso ∧ GlobalTheory.SlopeRec.HasPhi y' (r * φ) ∧ ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n e : ℕ) (s : c.F), ∀ f ∈ thGen Xo c nab a n, nval T'.V (r * e) (io' s * evI y' f) = nval T.V e (io s * evI y f) := by
  intro E _ _ _ H Dw l Xo c
  letI := H.starRing
  intro T io y hy φ hφ
  obtain ⟨S', io', z', r, hz', hr, hU, ψA, hv, hm⟩ :=
    exists_ext_all_models_uniformised_charZero E H Dw l Xo c T io y hy
  have hphi : ∀ φ' : ℝ, GlobalTheory.SlopeRec.HasPhi z' φ' → φ' = r * φ := fun φ' h' =>
    GlobalTheory.T.balancedPeriodSlope_mul_ramificationIndex _ _ _ _ Xo c T S' io io' y z' r hr ⟨ψA, hv, hm⟩ φ φ' hφ h'
  letI := io.toAlgebra
  let ψ : T.Fr →+* S'.Fr := letI := io'.toAlgebra; ψA.toRingHom
  have hio : io' = ψ.comp io := by
    letI := io'.toAlgebra
    exact RingHom.ext fun a => (ψA.commutes a).symm
  have hv' : ∀ a : T.Fr, vV S'.V (ψ a) = (r : ℤ) * vV T.V a := fun a => by
    by_cases ha : a = 0
    · simp [ha, vV]
    · exact hv a ha
  have hev : ∀ (nab : NabV Xo c), IsNab Xo c nab → ∀ (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ),
      ∀ f ∈ thGen Xo c nab a n, ψ (evI y f) = evI z' f := fun nab hn a n f hf =>
    GlobalTheory.T.thetaRule_integralPoint_value_baseChange _ _ _ _ Xo c nab hn T S' io io' y z' ψA hm a n f hf
  clear_value ψ
  clear hm hv ψA
  subst hio
  obtain ⟨C, hCh⟩ := GlobalTheory.IntChartTrunc.intChart_frTrunc_exists _ H _ _ Xo c (fun _ => rfl) S' _ z'
  obtain ⟨P, hP⟩ := hU C.I
  obtain ⟨φ', hφ'⟩ := GlobalTheory.SlopeRec.exists_hasPhi z' C.I.G C.I.t' C.I.m1 C.I.m2 P
  have e1 := hphi φ' hφ'
  subst e1
  refine ⟨S', ψ.comp io, z', r, C, P, hz', hr, hCh, hP, hφ', fun nab hn a n e s f hf => ?_⟩
  rw [← hev nab hn a n f hf, RingHom.comp_apply, ← map_mul, Formalism.L2.Pj.nval_bc ψ hr hv']

end GlobalTheory.ExtScaleZero
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetGeneratorDescendsSubring
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
open GlobalTheory.SiegelDescent ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison

namespace GlobalTheory

theorem lbIso_triv_pull_triv {X Y : Scheme.{0}} (f : Y ⟶ X) : LBIso ((LB.triv X).pull f) (LB.triv Y) :=
  Ex.ValInh.lbIso_of_g_one (fun i j => by
    simp only [LB.pull, LB.LinComb, LB.triv, map_one, one_zpow, Finset.prod_const_one]
    simp only [Finset.univ_unique, Finset.prod_singleton, zpow_one]
    exact (res _).map_one) (fun i j => rfl)

theorem exists_finset_gen_descends : ∀ (R : Type) [CommRing R] (S : Subring R) (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (B : Over (Sp S)) [GrpObj B] [IsCommMonObj B] (φ : A.left ⟶ B.left) (φ₂ : (G2 A).left ⟶ (G2 B).left) (P : LB (G2 A).left) (P₀ : LB (G2 B).left) (a : A ⟶ G2 A) (a₀ : B ⟶ G2 B), IsAbelianScheme B → IsGrpPullback A B (spMap S.subtype) φ → IsSquare φ φ₂ → P.IsLB → P₀.IsLB → LBIso P (P₀.pull φ₂) → a.left ≫ φ₂ = φ ≫ a₀.left → (∃ t : (P.pull a.left).Gen, t.IsGen) → ∃ F : Finset R, ∀ (R₁ : Subring R) (h : S ≤ R₁), (F : Set R) ⊆ R₁ → ∀ a₁ : (Over.pullback (spMap (Subring.inclusion h))).obj B ⟶ G2 ((Over.pullback (spMap (Subring.inclusion h))).obj B), a₁.left ≫ pφ₂ (spMap (Subring.inclusion h)) B = pφ (spMap (Subring.inclusion h)) B ≫ a₀.left → ∃ t : ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left).Gen, t.IsGen := by
  intro R _ S A _ _ B _ _ φ φ₂ P P₀ a a₀ hB hφ sq hP hP₀ hw e ht
  haveI := hB.proper
  have hN : (P₀.pull a₀.left).IsLB := pull_isLB hP₀ _
  have hT : ∀ X : Scheme.{0}, (LB.triv X).IsLB := fun X => LB.isLB_triv X
  have H₀ : LBIso (LB.triv A.left) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (hT _) (pull_isLB hP _) (pull_isLB hN _) ((CechPic.iso_triv_iff _).2 ht)
      (lbIso_square hP hP₀ hw e)
  have H : LBIso ((LB.triv B.left).pull φ) ((P₀.pull a₀.left).pull φ) :=
    LBIso.trans (pull_isLB (hT _) _) (hT _) (pull_isLB hN _) (lbIso_triv_pull_triv φ) H₀
  obtain ⟨F, hF⟩ := lbIso_descends_to_subring_containing_finset R S A.left B.left A.hom B.hom φ
    (LB.triv B.left) (P₀.pull a₀.left) hφ.1 (hT _) hN H
  refine ⟨F, fun R₁ h hs a₁ e₁ => ?_⟩
  have H₁ := hF R₁ h hs _ _ (pφ (spMap (Subring.inclusion h)) B)
    (isGrpPullback (spMap (Subring.inclusion h)) B).1
  have H₂ : LBIso ((P₀.pull (pφ₂ (spMap (Subring.inclusion h)) B)).pull a₁.left)
      ((P₀.pull a₀.left).pull (pφ (spMap (Subring.inclusion h)) B)) :=
    lbIso_square (pull_isLB hP₀ _) hP₀ (PolBaseChange.lbIso_refl (pull_isLB hP₀ _)) e₁
  refine (CechPic.iso_triv_iff _).1 ?_
  exact LBIso.trans (hT _) (pull_isLB (hT _) _) (pull_isLB (pull_isLB hP₀ _) _)
    (lbIso_triv_pull_triv _).symm
    (LBIso.trans (pull_isLB (hT _) _) (pull_isLB hN _) (pull_isLB (pull_isLB hP₀ _) _) H₁ H₂.symm)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFlagCellContainingFramedPoint
section
noncomputable section

namespace GlobalTheory.FlagMod.FieldFlag

open AlgebraicGeometry CategoryTheory TopologicalSpace _root_.CategoryTheory.Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv mkT tanM_ext tv_mem actR)
attribute [local instance] Over.cartesianMonoidalCategory

theorem exists_cell_lies : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) (Z : Scheme.{0}) (π : Z ⟶ Y.X) (g : ∀ en : En Dw.mult, Z ⟶ PSpace c.F (plN A.N en.1)) (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ Z)) [∀ b w, IsOpenImmersion (κ b w)] (hZ : Cells A π g κ) (ht : FlagCellFrameChangeTriangular hZ) (S : Type) [CommRing S] [Algebra c.F S] (P : FrPt Xo c S) (q : PrimeSpectrum S), ∃ f : S, f ∉ q.asIdeal ∧ ∃ z : Sp (Localization.Away f) ⟶ Z, ∀ P' : FrPt Xo c (Localization.Away f), FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P' → (cellFrames hZ ht).Lies z P' := by
  intro E _ _ _ H Dw l Xo c Y p A Z π g κ _ hZ ht S _ _ P q
  classical
  obtain ⟨b, hb⟩ := A.cov ((frX P ≫ Y.j) q)
  obtain ⟨f₀, hf₀, hV⟩ := _root_.GlobalTheory.nbhd_basicOpen_of_mem S Y.X (frX P ≫ Y.j) (A.k b).V q hb
  let ι₀ : S →ₐ[c.F] Localization.Away f₀ := IsScalarTower.toAlgHom c.F S (Localization.Away f₀)
  obtain ⟨P₀, hP₀⟩ := exists_frMap ι₀ P
  have hx₀ : frX P₀ ≫ Y.j = spMap (algebraMap S (Localization.Away f₀)) ≫ frX P ≫ Y.j := by
    rw [← frX_frMap hP₀, Category.assoc]; rfl
  have h₀ : ⊤ ≤ (frX P₀ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₀]; exact hV
  choose T hTu hT using _root_.GlobalTheory.FlagMod.FieldFlag.frVec_eq_eigFrame_mul E H Dw l Xo c Y p A b _ P₀ h₀
  have hq₀ : (Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f₀) _ q.asIdeal q.2
      ((Ideal.disjoint_powers_iff_notMem _ q.2.isRadical).2 hf₀)
  have hdet : ∀ σ, (T σ).det ∉ Ideal.map (algebraMap S (Localization.Away f₀)) q.asIdeal :=
    fun σ h => hq₀.ne_top (Ideal.eq_top_of_isUnit_mem _ h (hTu σ))
  choose w hw using fun σ => _root_.GlobalTheory.exists_rowPerm_leadingMinors_not_mem _ _ (T σ) _ hq₀ (hdet σ)
  obtain ⟨f, hf, φ, hφ⟩ := _root_.GlobalTheory.exists_basicOpen_isUnit_of_notMem_map S f₀ q.asIdeal q.2 hf₀ (Σ σ : E →+* ℂ, Fin (Dw.mult σ + 1))
    (fun i => (((T i.1).submatrix (w i.1) id).submatrix (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))
      (Fin.castLE (Nat.lt_succ_iff.1 i.2.2))).det) (fun i => hw i.1 _ _)
  refine ⟨f, hf, ?_⟩
  let φ' : Localization.Away f₀ →ₐ[c.F] Localization.Away f := φ.restrictScalars c.F
  have hcomp : φ'.comp ι₀ = IsScalarTower.toAlgHom c.F S (Localization.Away f) :=
    AlgHom.ext fun s => φ.commutes s
  obtain ⟨P₁, hP₁⟩ := exists_frMap φ' P₀
  have hP₁' : FrMap (IsScalarTower.toAlgHom c.F S (Localization.Away f)) P P₁ :=
    hcomp ▸ PullbackSections.frMap_trans ι₀ φ' hP₀ hP₁
  have hx₁ : frX P₁ ≫ Y.j = spMap φ'.toRingHom ≫ frX P₀ ≫ Y.j := by rw [← frX_frMap hP₁, Category.assoc]
  have h₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).V := by rw [hx₁]; exact le_preimage_comp _ h₀
  have hM₁ : ⊤ ≤ (frX P₁ ≫ Y.j) ⁻¹ᵁ (A.k b).M.U := le_preimage_mono (A.k b).le h₁
  have hminor : ∀ σ (k : ℕ) (hk : k ≤ Dw.mult σ), IsUnit ((((T σ).map φ').submatrix (w σ) id).submatrix
      (Fin.castLE hk) (Fin.castLE hk)).det := by
    intro σ k hk
    have h := hφ ⟨σ, ⟨k, Nat.lt_succ_of_le hk⟩⟩
    have e : (((T σ).map φ').submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk) =
        (φ : Localization.Away f₀ →+* Localization.Away f).mapMatrix
          (((T σ).submatrix (w σ) id).submatrix (Fin.castLE hk) (Fin.castLE hk)) := rfl
    rw [e, ← RingHom.map_det]
    exact h
  choose L U hL0 hL1 hU hUu hLU using fun σ => _root_.GlobalTheory.lowerUnitriangular_mul_upperTriangular_of_isUnit_leadingMinors (Localization.Away f) (Dw.mult σ)
    (((T σ).map φ').submatrix (w σ) id) (hminor σ)
  let ψ₀ : Γ(Y.X, (A.V b).1) →+* Localization.Away f := ev (frX P₁ ≫ Y.j) _ h₁
  let xc : CellVar Dw.mult → Localization.Away f := fun v => L v.1 v.2.1.1 v.2.1.2
  obtain ⟨hzπ, hz, huAt⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.cellpt E H Dw l Xo c Y p A Z π g κ hZ ht b w _ ψ₀ xc _ rfl
  refine ⟨spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w, fun P' hP' => ?_⟩
  obtain rfl := frMap_unique hP₁' hP'
  have hx : (spMap (MvPolynomial.eval₂Hom ψ₀ xc) ≫ κ b w) ≫ π = frX P₁ ≫ Y.j :=
    hzπ.trans (spMap_ev _ (A.V b).2 h₁)
  refine _root_.GlobalTheory.FlagMod.Frames.lies_of_chart_tri E H Dw l Xo c c.F (RingHom.id c.F) Y Z π (cellFrames hZ ht)
    (_root_.GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen E H Dw l Xo c Y p A Z π g κ hZ ht) _ P₁ _ ((b, w) : A.B × Pm Dw.mult) hz hx U hU hUu ?_
  intro σ i
  rw [hT σ _ φ' P₁ hP₁ h₁ hM₁ i]
  have hcell : Matrix.of (cell xc σ) = L σ := by
    ext i j
    simp only [Matrix.of_apply, cell, xc]
    split_ifs with h1 h2
    · rfl
    · subst h2; exact (hL1 σ i).symm
    · exact (hL0 σ i j (lt_of_le_of_ne (not_lt.1 h1) h2)).symm
  have key : ((A.k b).u σ).map ψ₀ * (T σ).map φ' =
      ((((A.k b).u σ).map ψ₀).submatrix id (w σ) * L σ) * U σ := by
    rw [Matrix.mul_assoc, ← hLU σ, Matrix.submatrix_mul_equiv, Matrix.submatrix_id_id]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Frames.vecAt, huAt σ, hcell, ← map_smul, ← map_sum]
  congr 1
  funext r
  change (((A.k b).u σ).map ψ₀ * (T σ).map φ') r i = _
  rw [key, Matrix.mul_apply]
  erw [Finset.sum_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact _root_.mul_comm _ _

end GlobalTheory.FlagMod.FieldFlag
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeometricSymplecticLevelLiftSiegel
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.SiegGeomLift

def baseAt {B : Type} [CommRing B] {N : ℕ} (b : TBase B N) {k : Type} [Field k] (β : B →+* k) : TBase k N where
  ζ := Units.map β.toMonoidHom b.ζ
  unit := by simpa using b.unit.map β
  prim := fun K _ β' => b.prim K (β'.comp β)

theorem exists_geom_level : ∀ (h n N : ℕ) (B : Type) [CommRing B] (b : TBase B N) (ζ₀ : B) (S : Scheme.{0}) (s : S ⟶ Sp B) (c : SiegPre h n ζ₀ s) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (β : B →+* k), 3 ≤ n → Odd N → n ∣ N → ζ₀ = (b.ζ : B) ^ (N / n) → c.Principal → x ≫ s = spMap β → ∃ e : (Fin h ⊕ Fin h → ℤ) → (Over.mk x ⟶ c.A), (∀ a a', e (a + a') = e a * e a') ∧ (∀ a, e a ^ N = 1) ∧ (∀ a, e a ^ (N / n) = toUnit (Over.mk x) ≫ c.lev a) ∧ (∀ a, e a = 1 ↔ ∃ a', a = N • a') ∧ (∀ g : Over.mk x ⟶ c.A, g ^ N = 1 → ∃ a, e a = g) ∧ ∀ a a', Out.WeilIs c.A c.diag N (e a) (e a') (unitOn (Units.map β.toMonoidHom b.ζ ^ (2 * omegaStd a a'))) := by
  intro h n N B _ b ζ₀ S s c k _ _ x β hn ho hd hζ hc hx
  let bk := baseAt b β
  have hj : β ζ₀ = (bk.ζ : k) ^ (N / n) := by rw [hζ, map_pow]; rfl
  obtain ⟨P₁, P₂, -⟩ := GlobalTheory.SiegelRingChange.siegPre_pull_ringChange h n B k ζ₀ _ β S (Sp k) s (𝟙 (Sp k)) x hj
    (by rw [hx, Category.id_comp])
  obtain ⟨c', hpb⟩ := P₁ c
  have hc' := P₂ c c' hpb hc
  obtain ⟨C, φC, pbC, ⟨φ₂C, sqC, isoC⟩, lowC⟩ := GlobalTheory.SiegLift.exists_level_lift h n N k bk c' hn ho hd hc'
  obtain ⟨φx, φ₂x, pbx, sqx, isox, levx⟩ := hpb
  let T0 : Over (Sp k) := 𝟙_ (Over (Sp k))
  have pb := IsGrpPullback.comp pbC pbx
  have wU : 𝟙 (Sp k) ≫ (T0.hom ≫ 𝟙 (Sp k) ≫ x) = x := by simp [T0]
  let U : Over.mk x ⟶ Over.mk (T0.hom ≫ 𝟙 (Sp k) ≫ x) := Over.homMk (𝟙 (Sp k)) wU
  let V : Over.mk (T0.hom ≫ 𝟙 (Sp k) ≫ x) ⟶ Over.mk x := Over.homMk (𝟙 (Sp k)) (by simp [T0])
  have VU : V ≫ U = 𝟙 _ := by ext; simp [U, V]; try rfl
  have UV : U ≫ V = 𝟙 _ := by ext; simp [U, V]; try rfl
  let ψ : (T0 ⟶ C.A) →* (Over.mk x ⟶ c.A) := (preHom U).comp (pushHom pb T0)
  have ψl : ∀ g : T0 ⟶ C.A, (ψ g).left = g.left ≫ φC ≫ φx := fun g => by
    show 𝟙 (Sp k) ≫ g.left ≫ φC ≫ φx = _
    simp
  have ψi : Function.Injective ψ := fun g g' e => by
    refine GlobalTheory.SiegelPull.push_injective pb T0 ?_
    have e' := congrArg (V ≫ ·) e
    simpa [ψ, preHom, ← Category.assoc, VU] using e'
  have ψs : Function.Surjective ψ := fun g => by
    obtain ⟨y, hy⟩ := GlobalTheory.SiegelPull.push_surjective pb T0 (V ≫ g)
    refine ⟨y, ?_⟩
    show U ≫ pushHom pb T0 y = g
    rw [hy, ← Category.assoc, UV, Category.id_comp]
  have hu : ∀ y : T0 ⟶ C.A, toUnit (Over.mk (𝟙 (Sp k))) ≫ y = y := fun y =>
    (congrArg (· ≫ y) (toUnit_unique _ (𝟙 T0))).trans (Category.id_comp _)
  obtain ⟨g₁, g₂, g₃⟩ := C.geom k (𝟙 _) (RingHom.id k) bk.ζ
    ((Category.id_comp _).trans (Spec.map_id _).symm) rfl
  simp only [hu] at g₁ g₂ g₃
  refine ⟨fun a => ψ (C.lev a), fun a a' => show ψ (C.lev (a + a')) = ψ (C.lev a) * ψ (C.lev a') by rw [C.lev_add, map_mul], fun a => show ψ (C.lev a) ^ N = 1 by rw [← map_pow, C.lev_tors, map_one],
    fun a => ?_, fun a => ?_, fun g hg => ?_, fun a a' => ?_⟩
  · apply Over.OverMorphism.ext
    rw [← map_pow, ψl, ← Category.assoc, lowC, pow_one, Category.id_comp, levx, Over.comp_left, Over.toUnit_left]
    rfl
  · rw [← map_one ψ, ψi.eq_iff]
    exact g₁ a
  · obtain ⟨y, rfl⟩ := ψs g
    obtain ⟨a, ha⟩ := g₂ y (ψi (by rw [map_pow, hg, map_one]))
    exact ⟨a, show ψ (C.lev a) = ψ y by rw [ha]⟩
  · have W1 := (GlobalTheory.weilIs_grpPullback_of_comm (Sp k) (Sp k) c'.A C.A (𝟙 (Sp k)) φC _ _ (pull_isLB c'.isLB _)
      (pull_isLB C.isLB _) pbC (GlobalTheory.SiegelPull.diag_iso sqC isoC) T0 N (C.lev a) (C.lev a')
      (pushHom pbC T0 (C.lev a)) (pushHom pbC T0 (C.lev a')) _ rfl rfl).1 (g₃ a a')
    have W2 := (GlobalTheory.weilIs_grpPullback_of_comm S (Sp k) c.A c'.A x φx _ _ (pull_isLB c.isLB _)
      (pull_isLB c'.isLB _) pbx (GlobalTheory.SiegelPull.diag_iso sqx isox) (Over.mk (T0.hom ≫ 𝟙 (Sp k))) N _ _
      (pushHom pbx _ (pushHom pbC T0 (C.lev a))) (pushHom pbx _ (pushHom pbC T0 (C.lev a'))) _ rfl rfl).1 W1
    exact GlobalTheory.SiegCover.weilIs_congr_base (by simp [T0]) ((Category.assoc _ _ _).trans (ψl _).symm)
      ((Category.assoc _ _ _).trans (ψl _).symm) W2

end GlobalTheory.SiegGeomLift
end
end

