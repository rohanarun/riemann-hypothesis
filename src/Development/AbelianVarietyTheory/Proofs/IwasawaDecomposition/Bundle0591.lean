module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0318
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0431
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameCover
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0535
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0539
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0580
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0240
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeChartBoundsOfSchurLemW
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0249
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteTypesViaFullHeckeAlgebraEigensystems
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3

theorem finiteTypes_of_full_heckeAlgebra_eigensystems : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → Formalism.BasicNotions.Rows.IsotRank D.what₂ → Lam3 Z := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hHost hIR
  have lab := GlobalTheory.T.exists_familyLabel_containing_finiteTypeParts h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  let cOf : D.what₂.FT → A3.fam3.base3.Ix := fun σ => (lab σ).choose
  have hc : ∀ σ, HasLab Y σ (cOf σ) := fun σ => (lab σ).choose_spec
  have rat := GlobalTheory.T.complexSpan_rationalLiftForms_eq_basePart h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have ind := GlobalTheory.T.iSupIndep_finiteTypeComponents_thetaLiftForms h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have dim := GlobalTheory.T.liftLabelPart_finrank_eq_rowsPart_finrank h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  have cnt := GlobalTheory.T.card_baseRows_label_eq_rowsPart_finrank h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost cOf hc
  have lam := GlobalTheory.T.liftScalar_eq_labelScalar h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hHost
  refine ⟨cOf, fun i c => ?_, fun i t σ ht hne => lam σ (cOf σ) i t (hc σ) ht hne, fun c => cnt c⟩
  have hind : iSupIndep (fun σ : {σ : D.what₂.FT // cOf σ = c} => D.what₂.isot ((i : ℕ) + 1) σ.1) :=
    (ind i).comp Subtype.val_injective
  refine ⟨hind, ?_⟩
  rw [rat i c]
  have hle : (⨆ σ : {σ : D.what₂.FT // cOf σ = c}, D.what₂.isot ((i : ℕ) + 1) σ.1) ≤ (R.Wp3 i c).comap (Y.mj.eW i) := by
    refine iSup_le fun σ => ?_
    have := (hc σ.1).1 i
    rw [σ.2] at this
    exact Submodule.map_le_iff_le_comap.1 this
  refine Submodule.eq_of_le_of_finrank_eq hle ?_
  rw [dim i c, ← cnt c, Formalism.IndefR.Cx.finrank_iSup_eq_sum _ hind]
  rw [Finset.sum_subtype (Finset.univ.filter (fun σ => cOf σ = c)) (p := fun σ => cOf σ = c) (by simp)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact hIR ((i : ℕ) + 1) (by omega) (by omega) σ.1

end GlobalTheory.Mem.R3
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagCellValuativeExistenceOverUnionOfOpens
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.ProjSpace GlobalTheory.FlagEmb
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.FlagEmb.Valu

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem sp_surj {k B : Type} [CommRing k] [CommRing B] (x : Sp k ⟶ Sp B) : ∃ β : B →+* k, x = spMap β :=
  ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem exists_of_closedPoint {A : Type} [CommRing A] [IsLocalRing A] {X : Scheme.{0}} (x : Sp A ⟶ X)
    (U : X.affineOpens) (hx : x (IsLocalRing.closedPoint A) ∈ (U.1 : Set X)) :
    ∃ φ : Γ(X, U.1) →+* A, x = spMap φ ≫ U.2.fromSpec := by
  have htop : x ⁻¹ᵁ U.1 = ⊤ := Scheme.preimage_eq_top_of_closedPoint_mem x hx
  have hr : Set.range x ⊆ Set.range U.2.fromSpec := by
    rw [U.2.range_fromSpec]
    rintro _ ⟨y, rfl⟩
    have : y ∈ x ⁻¹ᵁ U.1 := by rw [htop]; trivial
    exact this
  have hi : IsOpenImmersion U.2.fromSpec := IsAffineOpen.isOpenImmersion_fromSpec U.2
  obtain ⟨φ, hφ⟩ := sp_surj (B := Γ(X, U.1)) (@IsOpenImmersion.lift _ _ _ U.2.fromSpec x hi hr)
  exact ⟨φ, (@IsOpenImmersion.lift_fac _ _ _ U.2.fromSpec x hi hr).symm.trans (congrArg (· ≫ U.2.fromSpec) hφ)⟩

theorem indep_cellVec {T : Type} {m : T → ℕ} {k : Type} [Field k] {M : ℕ} (D c : Let m → Fin (M + 1) → k) (w : Pm m)
    (x : CellVar m → k) (h : LeftInv D c) (τ : T) :
    LinearIndependent k fun j : Fin (m τ) => cellVec c w x ⟨τ, j⟩ := by
  have h1 := (_root_.GlobalTheory.FlagEmb.CauchyBinet.main.2 T m k M D c w x h).1 _ _ (down_std τ (m τ) le_rfl)
  rw [_root_.GlobalTheory.FlagEmb.CauchyBinet.main.1] at h1
  have h2 := Matrix.linearIndependent_rows_of_det_ne_zero (h1.trans_ne one_ne_zero)
  let L : (Fin (M + 1) → k) →ₗ[k] (Fin (m τ) → k) :=
    Matrix.toLin' (Matrix.of fun l' r => D ((wLet w ∘ std τ (m τ) le_rfl) l') r)
  exact LinearIndependent.of_comp L h2

theorem inBlock_cellVec {T : Type} {m : T → ℕ} {S ι : Type} [CommRing S] {c c' : Let m → ι → S} (h : InBlock c c')
    (w : Pm m) (x : CellVar m → S) : InBlock c (cellVec c' w x) := fun z =>
  Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (h ⟨z.1, w z.1 i⟩)

theorem map_uvec {X : Scheme.{0}} {T : Type} {m : T → ℕ} {M : ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (c : Let m → Fin (M + 1) → Γ(X, U.1)) (w : Pm m) (ψ : CR m U →+* S) :
    (fun z => ψ ∘ uvec c w z) =
      cellVec (fun z => (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ∘ c z) w (ψ ∘ MvPolynomial.X) :=
  funext fun z => map_cellVec ψ _ w _ z

theorem sp_cbase {X : Scheme.{0}} {T : Type} {m : T → ℕ} {U : X.affineOpens} {S : Type} [CommRing S]
    (ψ : CR m U →+* S) :
    spMap ψ ≫ cbase m U = spMap (ψ.comp (MvPolynomial.C : Γ(X, U.1) →+* CR m U)) ≫ U.2.fromSpec := by
  rw [cbase, ← Category.assoc, sp_comp]

theorem exists_integral_cell : ∀ (O K : Type) [CommRing O] [Field K] (β : O →+* K) (X : Scheme.{0}) (s : X ⟶ Sp O) (T : Type) [Finite T] (m : T → ℕ) (M : ℕ) (B : Type) (V : B → X.affineOpens) (α : ∀ b, K →+* Γ(X, (V b).1)) (c D : ∀ b, Let m → Fin (M + 1) → Γ(X, (V b).1)) (P : Scheme.{0}) (p0 : P ⟶ X) (p : ∀ en : En m, P ⟶ PSpace O (plN M en.1)) (h : ∀ b, Pm m → (Sp (CR m (V b)) ⟶ P)), IsCover β s V α c D → IsPlk β s V α c p0 p h → ∀ (A k : Type) [CommRing A] [IsDomain A] [ValuationRing A] [Field k] [Algebra A k] [IsFractionRing A k] b' w' (a : Sp k ⟶ Sp (CR m (V b'))) (x : Sp A ⟶ X), Set.range x ⊆ ⋃ b, ((V b).1 : Set X) → a ≫ cbase m (V b') = spMap (algebraMap A k) ≫ x → ∃ b w, ∃ l : Sp A ⟶ Sp (CR m (V b)), l ≫ cbase m (V b) = x ∧ spMap (algebraMap A k) ≫ l ≫ h b w = a ≫ h b' w' := by
  intro O K _ _ β X s T _ m M B V α c D P p0 p h hC hP A k _ _ _ _ _ _ b' w' a x hx ha
  obtain ⟨ψ', rfl⟩ := sp_surj a
  obtain ⟨b, hb⟩ := Set.mem_iUnion.1 (hx ⟨IsLocalRing.closedPoint A, rfl⟩)
  obtain ⟨φ, rfl⟩ := exists_of_closedPoint x (V b) hb
  have ha' : spMap ((algebraMap A k).comp φ) ≫ (V b).2.fromSpec =
      spMap (ψ'.comp (MvPolynomial.C : Γ(X, (V b').1) →+* CR m (V b'))) ≫ (V b').2.fromSpec := by
    rw [← sp_cbase, ha, ← Category.assoc, sp_comp]
  obtain ⟨w, y, d, hy, hd, ht⟩ := _root_.GlobalTheory.FlagEmb.exists_integral_cell T m k (ValuationRing.valuation A k).valuationSubring M _ _
    (inBlock_cellVec (hC.compat k b b' _ _ ha') w' (ψ' ∘ MvPolynomial.X))
    (indep_cellVec _ _ w' _ ((hC.inv b').map _))
  have hy' : ∀ v, ∃ t : A, algebraMap A k t = y v := fun v => (ValuationRing.mem_integer_iff A k (y v)).1 (hy v)
  choose t hyt using hy'
  let χ : CR m (V b) →+* A := MvPolynomial.eval₂Hom φ t
  have hχ : χ.comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) = φ := MvPolynomial.eval₂Hom_comp_C φ t
  have hχ' : ((algebraMap A k).comp χ).comp (MvPolynomial.C : Γ(X, (V b).1) →+* CR m (V b)) =
      (algebraMap A k).comp φ := by rw [RingHom.comp_assoc, hχ]
  refine ⟨b, w, spMap χ, by rw [sp_cbase, hχ], ?_⟩
  rw [← Category.assoc, sp_comp]
  refine GlobalTheory.T.flagCell_point_eq_of_triangular_frames O K β X s T m M B V α c D P p0 p h hC hP k b b' w w' _ ψ' d ?_ hd ?_
  · rw [sp_cbase, sp_cbase, hχ', ha']
  · have e : ((algebraMap A k).comp χ) ∘ MvPolynomial.X = y := funext fun v => by
      rw [← hyt]
      exact congrArg (algebraMap A k) (MvPolynomial.eval₂Hom_X' φ t v)
    rw [map_uvec, map_uvec, hχ', e]
    exact ht

end GlobalTheory.FlagEmb.Valu
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FlagSpaceComponentBaseMapOfFunctionFields
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam
  GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

theorem GlobalTheory.FlagBundle.exists_isHom_base_of_lifts : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z), IsOpenImmersion j → j ≫ genStr Z ≫ spMap e.toRingHom = X.str → ∀ (f : C.Y.X ⟶ X.X), f ≫ j = C.π → (∀ (K : Type) [Field K] [IsAlgClosed K] (χ : c.F →+* K) (x : Sp K ⟶ X.X), x ≫ j ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ j ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x ∧ C.Carries p g) → ∃ φ : X.Fn →ₐ[F] C.Y.Fn, (ratOf X).IsHom (ratOf C.Y) φ f := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j _ hj f hf hl
  have hs : f ≫ X.str = C.Y.str := by
    rw [← hj, ← C.π_str, ← hf, Category.assoc]

  let K : Type := AlgebraicClosure X.Fn
  let a : X.Fn →+* K := algebraMap X.Fn K
  let x : Sp K ⟶ X.X := spMap a ≫ genericPt X
  have h1 : genericPt X ≫ X.str = spMap (algebraMap F X.Fn) := (ratOf X).pt_s
  have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
    rw [← Spec.map_comp]
    exact (congrArg Spec.map (CommRingCat.hom_ext (RingEquiv.toRingHom_comp_symm_toRingHom e))).trans (Spec.map_id _)
  have hg0 : (genericPt X ≫ j) ≫ genStr Z = spMap (constF e X) := by
    have : spMap (constF e X) = spMap (algebraMap F X.Fn) ≫ spMap e.symm.toRingHom := by
      rw [constF, ← Spec.map_comp]; rfl
    rw [this, ← h1, ← hj]
    simp only [Category.assoc, h2, Category.comp_id]
  let χ : c.F →+* K := a.comp (constF e X)
  have hx : (x ≫ j) ≫ genStr Z = spMap χ := by
    have : spMap χ = spMap a ≫ spMap (constF e X) := by rw [← Spec.map_comp]; rfl
    rw [this, ← hg0]
    simp only [x, Category.assoc]
  obtain ⟨g⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame E H Dw l Xo c O β Z K χ (x ≫ j) hx
  rw [Category.assoc] at g hx
  obtain ⟨p, ⟨hp, -⟩, -⟩ := hl K χ x hx g

  have hpt : f (p (IsLocalRing.closedPoint K)) = genericPoint X.X := by
    have hc : (p ≫ f) (IsLocalRing.closedPoint K) = f (p (IsLocalRing.closedPoint K)) := Scheme.Hom.comp_apply _ _ _
    rw [← hc, hp]
    show (ratOf X).pt (spMap a (IsLocalRing.closedPoint K)) = _
    exact (ratOf X).pt_apply _
  have hsp : f (genericPoint C.Y.X) ⤳ genericPoint X.X :=
    hpt ▸ (genericPoint_specializes (p (IsLocalRing.closedPoint K))).map f.continuous
  exact exists_isHom_of_generic (ratOf X) (ratOf C.Y) f hs (hsp.antisymm (genericPoint_specializes _)).eq
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FullFlagFramesFlagComponentPullbackBaseFrames
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LieBase.FlagPull

theorem frames_sub : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (F : Type) [Field F] (e : F ≃+* c.F) (C : FlagCpt Z e) (X : Var F) (j : X.X ⟶ gen Z) (f : C.Y.X ⟶ X.X), f ≫ j = C.π → ∀ (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z)) (Eb : Fr (ratOf X) Dw.mult 0) (A₀ : Mat Dw.mult X.Fn), Tied e X j f₀ Eb A₀ → ∀ (φ : X.Fn →ₐ[F] C.Y.Fn), (ratOf X).IsHom (ratOf C.Y) φ f → ∀ (E' : Fr (ratOf C.Y) Dw.mult Dw.mult) (A₁ : Mat Dw.mult C.Y.Fn), Tied e C.Y C.π C.f0 E' A₁ → f₀.Coord (φ : X.Fn →+* C.Y.Fn) C.f0 (A₁ * (A₀.map φ)⁻¹) → ∀ z', ∀ A' ∈ E'.S z', ∀ A ∈ Eb.S (f z'), Par 0 ((ratOf C.Y).O z').toSubring (A' * (A.map φ)⁻¹) := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C X j f hπ f₀ Eb A₀ hT φ hφ E' A₁ hT' hc0 z' A' hA' A hA
  change C.Y.X at z'
  have hA₀d : ∀ τ, (A₀ τ).det ≠ 0 := Fr.det_ne hT.1
  have hA₁d : ∀ τ, (A₁ τ).det ≠ 0 := Fr.det_ne hT'.1
  have hA'd : ∀ τ, (A' τ).det ≠ 0 := Fr.det_ne hA'
  have hmapd : ∀ {B : Mat Dw.mult X.Fn}, (∀ τ, (B τ).det ≠ 0) →
      ∀ τ, (B.map φ τ).det ≠ 0 := fun {B} hB τ => by
    have := Mat.det_map B (φ : X.Fn →+* C.Y.Fn) τ
    rw [show B.map φ = B.map (φ : X.Fn →+* C.Y.Fn) from rfl, this]; exact (map_ne_zero _).2 (hB τ)
  obtain ⟨φ₁, fA, hfA⟩ := hT.2 (f z') A hA
  obtain ⟨φ', f', hf'⟩ := hT'.2 z' A' hA'
  let aY : C.Y.X.presheaf.stalk z' →+* C.Y.Fn := algebraMap (C.Y.X.presheaf.stalk z') C.Y.X.functionField
  let aB : X.X.presheaf.stalk (f z') →+* X.Fn := algebraMap (X.X.presheaf.stalk (f z')) X.X.functionField
  let σ : X.X.presheaf.stalk (f z') →+* C.Y.X.presheaf.stalk z' := (f.stalkMap z').hom
  have hinj : Function.Injective aY := IsFractionRing.injective (C.Y.X.presheaf.stalk z') C.Y.X.functionField
  have hcomp : (φ : X.Fn →+* C.Y.Fn).comp aB = aY.comp σ :=
    RingHom.ext fun a => map_algebraMap_stalk hφ z' a
  have hc : constF e C.Y = (φ : X.Fn →+* C.Y.Fn).comp (constF e X) :=
    RingHom.ext fun a => (φ.commutes _).symm
  have hσ : spMap σ ≫ stalkPt X (f z') = stalkPt C.Y z' ≫ f := Scheme.SpecMap_stalkMap_fromSpecStalk f
  have hx' : stalkPt C.Y z' ≫ C.π ≫ genι Z = spMap σ ≫ stalkPt X (f z') ≫ j ≫ genι Z := by
    rw [← hπ, Category.assoc, reassoc_of% hσ]
  have hφ' : φ' = σ.comp φ₁ := by
    have h1 : aY.comp φ' = aY.comp (σ.comp φ₁) := by
      rw [← hf'.2.1, ← RingHom.comp_assoc, ← hcomp, RingHom.comp_assoc, ← hfA.2.1, hc]
    exact RingHom.ext fun a => hinj (RingHom.congr_fun h1 a)
  have hstA : fA.Stable := GlobalTheory.T.lie_eigenspace_frame_stable_of_isLocalRing E H Dw l Xo c O β Z _ _ _ fA inferInstance
  obtain ⟨⟨G, hG, -⟩, hu⟩ := (GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA _ φ'
    (stalkPt C.Y z' ≫ C.π ≫ genι Z) σ inferInstance hstA hx' hφ').1 f'
  have hGd := hu G hG
  have h1 := _root_.GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f' _ _ _ C.f0 σ aY G (A₁ * A'⁻¹) inferInstance hG hf'
  have h2 := _root_.GlobalTheory.ShFam.CoordComp.coord_comp E H Dw l Xo c O β Z _ _ _ fA _ _ _ f₀ _ _ _ C.f0 aB (φ : X.Fn →+* C.Y.Fn) _ _
    inferInstance hfA hc0
  rw [hcomp] at h2
  have hU := ((GlobalTheory.T.lie_eigenspace_frame_coordinates_unique_invertible E H Dw l Xo c O β Z _ _ _ fA C.Y.Fn (constF e C.Y)
    (genericPt C.Y ≫ C.π ≫ genι Z) (aY.comp σ) inferInstance hstA h1.1 h1.2.1).1 C.f0).1.unique h1 h2
  have e : (A₀ * A⁻¹).map (φ : X.Fn →+* C.Y.Fn) = A₀.map φ * (A.map φ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv]; rfl
  have key : A₁ * (A'⁻¹ * G.map aY) = A₁ * (A.map φ)⁻¹ := by
    rw [← mul_assoc, hU, e, mul_assoc A₁, ← mul_assoc (A₀.map φ)⁻¹, Mat.inv_mul (hmapd hA₀d), one_mul]
  have hGm : G.map aY = A' * (A.map φ)⁻¹ := by
    calc G.map aY = A' * (A₁⁻¹ * (A₁ * (A'⁻¹ * G.map aY))) := by
          rw [← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul, ← mul_assoc, Mat.mul_inv hA'd, one_mul]
      _ = A' * (A.map φ)⁻¹ := by
          rw [key, ← mul_assoc A₁⁻¹, Mat.inv_mul hA₁d, one_mul]
  exact (GlobalTheory.ShFam.TieBase.par_zero_iff aY hinj _ (fun x => mem_O_ratOf) _).2 ⟨G, hGd, hGm.symm⟩

end GlobalTheory.LieBase.FlagPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicDerivChernConnectionInverseSymmetricG
section
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

open Filter

theorem del_del_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {u : E → ℂ} {z : E} (hu : ContDiffAt ℝ 2 u z) (v w : E) :
    GlobalTheory.del (fun x => GlobalTheory.del u x w) z v = GlobalTheory.del (fun x => GlobalTheory.del u x v) z w := by
  have h := GlobalTheory.differentiableAt_fderiv_of_contDiffAt_two hu
  have h1 : ∀ a, DifferentiableAt ℝ (fun x => fderiv ℝ u x a) z :=
    fun a => h.clm_apply (differentiableAt_const _)
  have hs := hu.isSymmSndFDerivAt (by simp)
  have e : ∀ w, (fun x => GlobalTheory.del u x w) =
      fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w)) :=
    fun w => funext fun x => GlobalTheory.del_apply u x w
  have d : ∀ w, GlobalTheory.del (fun x => (1 / 2 : ℂ) • (fderiv ℝ u x w - Complex.I • fderiv ℝ u x (Complex.I • w))) z
      = (1 / 2 : ℂ) • (GlobalTheory.del (fun x => fderiv ℝ u x w) z
          - Complex.I • GlobalTheory.del (fun x => fderiv ℝ u x (Complex.I • w)) z) := fun w => by
    rw [GlobalTheory.del_const_smul _ ((h1 _).fun_sub ((h1 _).fun_const_smul Complex.I)),
      GlobalTheory.del_sub (h1 _) ((h1 _).fun_const_smul Complex.I), GlobalTheory.del_const_smul _ (h1 _)]
  rw [e w, e v, d w, d v]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.sub_apply, GlobalTheory.del_apply,
    GlobalTheory.fderiv_fderiv_apply hu]
  rw [hs.eq v w, hs.eq (Complex.I • v) w, hs.eq v (Complex.I • w),
    hs.eq (Complex.I • v) (Complex.I • w)]
  match_scalars <;> ring

theorem mdel_mdel_comm {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {m n : Type*} {A : E → Matrix m n ℂ} {z : E} (h : MContDiffAt 2 A z)
    (ξ η : E) : mdel (fun x => mdel A x η) z ξ = mdel (fun x => mdel A x ξ) z η := by
  ext a b
  exact del_del_comm (h a b) ξ η

theorem mdel_conn_inv_sub {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E]
    [IsScalarTower ℝ ℂ E] {g : ℕ} (H : E → Matrix (Fin g) (Fin g) ℂ) (z : E)
    (h2 : MContDiffAt 2 H z) (hu : IsUnit (H z).det) (hs : ∀ᶠ x in 𝓝 z, (H x).IsSymm) (ξ η : E) :
    mdel (fun x => conn (fun y => (H y)⁻¹) x η) z ξ
      - mdel (fun x => conn (fun y => (H y)⁻¹) x ξ) z η
      = -(conn H z η * conn H z ξ - conn H z ξ * conn H z η)ᵀ := by
  have h1 : MContDiffAt 1 H z := h2.of_le one_le_two
  have hloc : ∀ ζ, (fun x => conn (fun y => (H y)⁻¹) x ζ) =ᶠ[𝓝 z]
      fun x => -((H x)⁻¹ * mdel H x ζ)ᵀ := fun ζ => by
    filter_upwards [h2.eventually_two, h2.eventually_isUnit hu, hs.eventually_nhds]
      with x hx2 hxu hxs
    have e : (fun y => (H y)⁻¹) =ᶠ[𝓝 x] fun y => GlobalTheory.HermFrame.dualGram (H y) :=
      hxs.mono fun y hy => by
        change (H y)⁻¹ = (H y)⁻¹ᵀ
        rw [transpose_nonsing_inv, hy.eq]
    rw [conn_congr e, conn_dual (hx2.of_le one_le_two) hxu, conn_eq_of_isSymm hxs]
  have hP : ∀ ζ, MContDiffAt 1 (fun x => mdel H x ζ) z := fun ζ => h2.mdel (by norm_num) ζ
  rw [mdel_congr (hloc η), mdel_congr (hloc ξ), mdel_neg, mdel_neg,
    mdel_transpose (fun x => (H x)⁻¹ * mdel H x η), mdel_transpose (fun x => (H x)⁻¹ * mdel H x ξ),
    mdel_mul (h1.inv hu) (hP η), mdel_mul (h1.inv hu) (hP ξ), mdel_inv h1 hu, mdel_inv h1 hu,
    mdel_mdel_comm h2 ξ η, conn_eq_of_isSymm hs, conn_eq_of_isSymm hs]
  have key : (H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z ξ * (H z)⁻¹) * mdel H z η
      - ((H z)⁻¹ * mdel (fun x => mdel H x ξ) z η + -((H z)⁻¹ * mdel H z η * (H z)⁻¹) * mdel H z ξ)
      = (H z)⁻¹ * mdel H z η * ((H z)⁻¹ * mdel H z ξ) - (H z)⁻¹ * mdel H z ξ * ((H z)⁻¹ * mdel H z η) := by
    noncomm_ring
  rw [← key, transpose_sub]
  abel

end GlobalTheory.HermFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HolomorphicFrameChangeLocalBounds
section
open AlgebraicGeometry CategoryTheory MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ProjVar GlobalTheory.FlagBundle GlobalTheory.GoodMetric GlobalTheory.LieBase
open Classical
open Matrix
open scoped ComplexOrder Topology

namespace GlobalTheory.HermFrame

theorem holo_contDiffOn {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {m : WithTop ℕ∞} :
    ContDiffOn ℂ m g U := by
  have ha : AnalyticOnNhd ℂ g U := fun z hz =>
    ReciprocityTheory.ChartRestriction.G.AR.Up.DivLA.analyticAt_of_diffOn hU hg hz
  exact ha.contDiffOn hU.uniqueDiffOn

theorem holo_fderiv_apply_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) (w : ReciprocityTheory.L2DbarEstimates.V n) :
    DifferentiableOn ℂ (fun u => fderiv ℂ g u w) U := by
  have h2 : ContDiffOn ℂ 2 g U := holo_contDiffOn hU hg
  have h1 : ContDiffOn ℂ 1 (fun u => fderiv ℂ g u) U := h2.fderiv_of_isOpen hU (by norm_num)
  exact (h1.clm_apply contDiffOn_const).differentiableOn (by norm_num)

theorem holo_del_eq_on {n : ℕ} {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U)
    {g : ReciprocityTheory.L2DbarEstimates.V n → ℂ} (hg : DifferentiableOn ℂ g U) {u : ReciprocityTheory.L2DbarEstimates.V n}
    (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) : GlobalTheory.del g u w = fderiv ℂ g u w := by
  rw [GlobalTheory.del_eq_fderiv (hg.differentiableAt (hU.mem_nhds hu))]

end GlobalTheory.HermFrame

namespace GlobalTheory.HermFrame

theorem holo_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel P u w i k = fderiv ℂ (fun x => P x i k) u w :=
  holo_del_eq_on hU (hP i k) hu w

theorem holo_mdel_mdel_entry {n : ℕ} {K : Type} {P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ}
    {U : Set (ReciprocityTheory.L2DbarEstimates.V n)} (hU : IsOpen U) (hP : ∀ i k, DifferentiableOn ℂ (fun u => P u i k) U)
    {u : ReciprocityTheory.L2DbarEstimates.V n} (hu : u ∈ U) (w w' : ReciprocityTheory.L2DbarEstimates.V n) (i k : K) :
    mdel (fun x => mdel P x w') u w i k =
      fderiv ℂ (fun x => fderiv ℂ (fun y => P y i k) x w') u w := by
  change GlobalTheory.del (fun x => GlobalTheory.del (fun y => P y i k) x w') u w = _
  have hev : (fun x => GlobalTheory.del (fun y => P y i k) x w') =ᶠ[𝓝 u]
      (fun x => fderiv ℂ (fun y => P y i k) x w') := by
    filter_upwards [hU.mem_nhds hu] with x hx
    exact holo_del_eq_on hU (hP i k) hx w'
  rw [GlobalTheory.del_congr hev]
  exact holo_del_eq_on hU (holo_fderiv_apply_on hU (hP i k) w') hu w

theorem holoFrame_local_bounds : ∀ (n : ℕ) (K : Type) [Fintype K] [DecidableEq K] (P : ReciprocityTheory.L2DbarEstimates.V n → Matrix K K ℂ) (r : ℝ), 0 < r → (∀ i k, DifferentiableOn ℂ (fun u => P u i k) (Metric.ball 0 r)) → IsUnit (P 0).det → ∃ r' : ℝ, 0 < r' ∧ r' ≤ r ∧ ∃ B : ℝ, ∀ v : ReciprocityTheory.L2DbarEstimates.V n, ‖v‖ < r' → IsUnit (P v).det ∧ (∀ i k, ContDiffAt ℝ 2 (fun u => P u i k) v) ∧ (∀ᶠ u in nhds v, ∀ η, GlobalTheory.HermFrame.mdbar P u η = 0) ∧ (∀ i k, ‖P v i k‖ ≤ B) ∧ (∀ i k, ‖(P v)⁻¹ i k‖ ≤ B) ∧ (∀ a i k, ‖GlobalTheory.HermFrame.mdel P v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) ∧ (∀ a b i k, ‖GlobalTheory.HermFrame.mdel (fun u => GlobalTheory.HermFrame.mdel P u (GlobalTheory.GoodMetric.coordVec b)) v (GlobalTheory.GoodMetric.coordVec a) i k‖ ≤ B) := by
  intro n K _ _ P r hr hP h0
  set U : Set (ReciprocityTheory.L2DbarEstimates.V n) := Metric.ball 0 r with hUdef
  have hU : IsOpen U := Metric.isOpen_ball
  have hPc : ContinuousOn P U :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => (hP i k).continuousOn
  have hdetc : ContinuousOn (fun u => (P u).det) U :=
    (continuous_id.matrix_det).comp_continuousOn hPc
  have hadjc : ∀ i k, ContinuousOn (fun u => (P u).adjugate i k) U := fun i k =>
    ((continuous_id.matrix_adjugate).matrix_elem i k).comp_continuousOn hPc
  have h0U : (0 : ReciprocityTheory.L2DbarEstimates.V n) ∈ U := Metric.mem_ball_self hr
  have hev : ∀ᶠ u in 𝓝 (0 : ReciprocityTheory.L2DbarEstimates.V n), (P u).det ≠ 0 :=
    (hdetc.continuousAt (hU.mem_nhds h0U)).eventually_ne h0.ne_zero
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.1 hev
  have hm : 0 < min ε r := lt_min hε hr
  set ρ := min ε r / 2 with hρ
  have hρpos : 0 < ρ := by rw [hρ]; linarith
  have hρε : ρ < ε := by have := min_le_left ε r; rw [hρ]; linarith
  have hρr : ρ < r := by have := min_le_right ε r; rw [hρ]; linarith
  set S := Metric.closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) ρ with hSdef
  have hSU : S ⊆ U := Metric.closedBall_subset_ball hρr
  have hSdet : ∀ u ∈ S, (P u).det ≠ 0 := fun u hu =>
    hball u (Metric.closedBall_subset_ball hρε hu)
  have hSc : IsCompact S := isCompact_closedBall 0 ρ

  let G1 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => P u i k
  let G2 : ReciprocityTheory.L2DbarEstimates.V n → (K → K → ℂ) := fun u i k => (P u)⁻¹ i k
  let G3 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → K → K → ℂ) := fun u a i k =>
    mdel P u (GlobalTheory.GoodMetric.coordVec a) i k
  let G4 : ReciprocityTheory.L2DbarEstimates.V n → (Fin n → Fin n → K → K → ℂ) := fun u a b i k =>
    mdel (fun u => mdel P u (GlobalTheory.GoodMetric.coordVec b)) u (GlobalTheory.GoodMetric.coordVec a) i k
  have hG1 : ContinuousOn G1 S :=
    continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ((hP i k).continuousOn).mono hSU
  have hG2 : ContinuousOn G2 S := by
    refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine (((hdetc.mono hSU).inv₀ hSdet).mul ((hadjc i k).mono hSU)).congr fun u _ => ?_
    simp [G2, Matrix.inv_def, Ring.inverse_eq_inv']
  have hG3 : ContinuousOn G3 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun i => continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (hP i k) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono
      hSU).congr fun u hu => ?_
    exact holo_mdel_entry hU hP (hSU hu) _ i k
  have hG4 : ContinuousOn G4 S := by
    refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => continuousOn_pi.2 fun i =>
      continuousOn_pi.2 fun k => ?_
    refine ((holo_fderiv_apply_on hU (holo_fderiv_apply_on hU (hP i k)
      (GlobalTheory.GoodMetric.coordVec b)) (GlobalTheory.GoodMetric.coordVec a)).continuousOn.mono hSU).congr
      fun u hu => ?_
    exact holo_mdel_mdel_entry hU hP (hSU hu) _ _ i k
  obtain ⟨C1, hC1⟩ := hSc.exists_bound_of_continuousOn hG1
  obtain ⟨C2, hC2⟩ := hSc.exists_bound_of_continuousOn hG2
  obtain ⟨C3, hC3⟩ := hSc.exists_bound_of_continuousOn hG3
  obtain ⟨C4, hC4⟩ := hSc.exists_bound_of_continuousOn hG4
  refine ⟨ρ, hρpos, hρr.le, max (max C1 C2) (max C3 C4), fun v hv => ?_⟩
  have hvS : v ∈ S := by
    rw [hSdef, Metric.mem_closedBall, dist_zero_right]; exact hv.le
  have hvU : v ∈ U := hSU hvS
  refine ⟨isUnit_iff_ne_zero.2 (hSdet v hvS), fun i k => ?_, ?_, fun i k => ?_, fun i k => ?_,
    fun a i k => ?_, fun a b i k => ?_⟩
  · exact ((holo_contDiffOn hU (hP i k)).contDiffAt (hU.mem_nhds hvU)).restrict_scalars ℝ
  · filter_upwards [hU.mem_nhds hvU] with u hu η
    ext i k
    simp [GlobalTheory.dbar_eq_zero ((hP i k).differentiableAt (hU.mem_nhds hu))]
  · have h := (norm_le_pi_norm (G1 v i) k).trans ((norm_le_pi_norm (G1 v) i).trans (hC1 v hvS))
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G2 v i) k).trans ((norm_le_pi_norm (G2 v) i).trans (hC2 v hvS))
    exact h.trans ((le_max_right _ _).trans (le_max_left _ _))
  · have h := (norm_le_pi_norm (G3 v a i) k).trans ((norm_le_pi_norm (G3 v a) i).trans
      ((norm_le_pi_norm (G3 v) a).trans (hC3 v hvS)))
    exact h.trans ((le_max_left _ _).trans (le_max_right _ _))
  · have h := (norm_le_pi_norm (G4 v a b i) k).trans ((norm_le_pi_norm (G4 v a b) i).trans
      ((norm_le_pi_norm (G4 v a) b).trans ((norm_le_pi_norm (G4 v) a).trans (hC4 v hvS))))
    exact h.trans ((le_max_right _ _).trans (le_max_right _ _))

end GlobalTheory.HermFrame
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingOfIntegersProjectiveModuleIntFinrank
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory

theorem finite_projective_int_of_ringOfIntegers :
    ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.Finite ℤ X ∧ Module.Projective ℤ X ∧ Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  intro E _ _ X _ _ _ _
  have hfin : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  have hflat : Module.Flat ℤ X := Module.Flat.trans ℤ (𝓞 E) X
  have hfree : Module.Free ℤ X := inferInstance
  refine ⟨hfin, inferInstance, ?_⟩
  rw [finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank]

end GlobalTheory
end

