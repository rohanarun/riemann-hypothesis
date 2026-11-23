module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0010
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0002
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.HodgeComparisonCompatibility
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.CmpSt
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.NumberField
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.LocalAtPlaces
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenOfUnit
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0010
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0014
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0256
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptProjectiveModel
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0246
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0126
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0177
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0255
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0140
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsCompatibleAlongMap
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0144
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AbelianVarietyTheory.Definitions.Divisors.BarCompSubsetClosure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2415
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2384
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2005
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1874
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0249

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompCoverCmSigns
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.hodge_comp_cover_cm_signs : Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (Xo : ∀ l : Tor.Level H, Moduli D l) (l : Tor.Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] [CharZero Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (dg : ℕ) (sm : CMType H → CMType H ⊕ CMType H) (m : ℕ) (s : CMType H → Fin m → 𝔐.Li) (a : K → ℤ) (e₀ : Ω), Top.IsGlobal Xo l c Y → 1 ≤ D.p → 1 ≤ D.q → 𝔐.IsCover dg → (∀ p ∈ S, HT.HTFree 𝔐 p) → (∀ p : ℕ, p.Prime → p ∉ S → ¬ (p : ℤ) ∣ discr E ∧ 4 * Fintype.card (CMType H) + 2 ≤ p ∧ 2 < p) → (sm = Sum.inl ∨ sm = Sum.inr) → (∀ τ, LinearIndependent Ω (s τ) ∧ Submodule.span Ω (Set.range (s τ)) = 𝔐.Vgen (sm τ)) → (Lat.tens (fun τ => detLat (𝔐.V (sm τ)) (s τ)) (fun _ => -1)).IsDegOn Set.univ y a e₀ → NefOnFibres (mCoordIdeal y) a := by
  intro hG hW E _ _ _ H D Xo l c Y S Ω _ _ K _ J _ y 𝔐 dg sm m s a e₀ hY hp hq hcov hS hS' hsm hs hdeg
  have hI : PB.Inputs := hG.2.2.2.2.2.2.2.2.2.1
  obtain ⟨M, 𝔐', Fl, e, i, g, bk, bx, j, hbk, hy, hd, hS2, hR, hj, hli, hV⟩ :=
    _root_.LevelTowerAlt.hodge_compact_cover_primes hW E H D Xo l c Y S Ω K J y 𝔐 dg hcov
      (fun p hp hdv => by by_contra h; exact (hS' p hp h).1 hdv) hS
  haveI : CharZero M.Ω := charZero_of_injective_ringHom i.injective
  have hNef : _ ∧ _ :=
    _root_.GlobalTheory.CompanionTheory.Relay.nefOnFibres_block_xdeg_sums_of_rootLines hG E H D Xo l c Y S M 𝔐' Fl e
      hY hp hq hS2 hS' hR
  obtain ⟨n1, n2⟩ := hNef
  have hb₀ : ∀ σ, LinearIndependent M.Ω (Fl.b σ) := by
    obtain ⟨_, _, -, -, -, h, -⟩ := Fl.generic
    exact h
  have hu := fun τ => GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.det_pull (L := 𝔐.V (sm τ)) hd hj hli (hs τ).1 (hs τ).2 (𝔐.vb (sm τ)) (hb₀ (sm τ))
    (by rw [← hV]; exact Fl.sub (sm τ))
  choose u hu0 hu using hu
  let a' : M.K → ℤ := Function.extend bk a 0
  have ha : ∀ k, a' (bk k) = a k := fun k => hbk.extend_apply _ _ k
  have ha' : ∀ k', k' ∉ Set.range bk → a' k' = 0 := fun k' h => Function.extend_apply' _ _ _ h
  have hB := GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_pull hu0 hd 𝔐.tie.cover hu hbk hy ha ha' hdeg
  simp only [← hV] at hB
  have hgr : ∀ (r : CMType H × Fin (D.p + D.q)) (σ : Σ s, Fin (labelRk D s)), HodgeCpt.rootIdx D r = σ →
      ((𝔐'.V σ.1).gr (Fl.b σ.1) σ.2).IsDegOn Set.univ M.y (HodgeCpt.rootSgn D r • M.xdeg r)
        (e r ^ HodgeCpt.rootSgn D r) := by
    rintro r _ rfl
    refine GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.deg_untens ?_ (hR r)
    unfold HodgeCpt.rootSgn
    split_ifs <;> norm_num
  have hA : ∃ A e₁, (Lat.tens (fun τ => detLat (𝔐'.V (sm τ)) (Fl.b (sm τ))) fun _ => -1).IsDegOn Set.univ M.y A e₁ ∧
      NefOnFibres (mCoordIdeal M.y) A := by
    have hdet : ∀ σ, detLat (𝔐'.V σ) (Fl.b σ) = Lat.tens (fun k => (𝔐'.V σ).gr (Fl.b σ) k) fun _ => 1 := fun σ =>
      _root_.LevelTowerAlt.determinant_lattice_graded_tensor _ _ _ _ _ _ _ (hb₀ σ) (Fl.sub σ)
    simp only [hdet]
    rcases hsm with rfl | rfl
    · have h1 : ∀ τ (k : Fin D.p), HodgeCpt.rootIdx D (τ, Fin.castAdd D.q k) = ⟨.inl τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_left (show ((Fin.castAdd D.q k : Fin _) : ℕ) < D.p from k.2)]
        rfl
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n2 using 1
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      simp [HodgeCpt.rootSgn]
    · have h1 : ∀ τ (k : Fin D.q), HodgeCpt.rootIdx D (τ, Fin.natAdd D.p k.rev) = ⟨.inr τ, k⟩ := fun τ k => by
        unfold HodgeCpt.rootIdx
        rw [dite_eq_right (by simp)]
        congr 1
        apply Fin.ext
        have := k.2
        simp only [Fin.val_natAdd, Fin.val_rev]
        omega
      refine ⟨_, _, Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _ (fun τ => Lat.tens_isDegOn _ _ _ _ _ _ _ _ _ _ _
        (fun k => hgr _ _ (h1 τ k)) _) _, ?_⟩
      convert n1 using 1
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [Finset.sum_filter, Fin.sum_univ_add]
      have h2 : ∀ k : Fin D.p, ¬ D.p ≤ (k : ℕ) := fun k => not_le.2 k.2
      have h3 := Equiv.sum_comp Fin.revPerm fun k : Fin D.q => M.xdeg (τ, Fin.natAdd D.p k)
      simp [HodgeCpt.rootSgn, h2, ← h3]
  obtain ⟨A, e₁, hA1, hA2⟩ := hA
  have hN := _root_.LevelTowerAlt.nef_fibres_scaled_lattice hI _ M.Ω M.K M.ι M.y 𝔐'.ξ _ A a' e₁ _ _ 𝔐'.tie
    (Finset.prod_ne_zero_iff.2 fun τ _ => hu0 τ) hA1 hB hA2
  obtain ⟨c₀, hc₀⟩ := 𝔐'.tie.cover ⟨genPt 𝔐'.ξ, specializes_rfl⟩
  exact _root_.LevelTowerAlt.nef_fibres_block_embedding hI Ω M.Ω i K M.K J M.ι y M.y bk bx a a' hbk hy (fun k => ⟨_, GlobalTheory.CompanionTheory.Ar.Cusp.DetNef.chart_ne hc₀ k⟩) ha ha' hN
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginGoodPrimesFinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.ChangeGeo

theorem genPt_comp {X : Scheme.{0}} {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (φ : Ω₀ →+* Ω) (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) :
    GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom φ) ≫ ξ) = GlobalTheory.CompanionTheory.Ar.genPt ξ := by
  show ξ ((Spec.map (CommRingCat.ofHom φ)) (IsLocalRing.closedPoint Ω)) = ξ (IsLocalRing.closedPoint Ω₀)
  congr 1
  exact Subsingleton.elim _ _

theorem spMap_comp' {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : R →+* S) (b : T →+* R) :
    spMap (a.comp b) = spMap a ≫ spMap b := by
  show Spec.map (CommRingCat.ofHom (a.comp b)) = Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b)
  rw [CommRingCat.ofHom_comp, Spec.map_comp]

theorem spMap_inj {R S : Type} [CommRing R] [CommRing S] {a b : R →+* S} (h : spMap a = spMap b) : a = b := by
  have h' : Spec.map (CommRingCat.ofHom a) = Spec.map (CommRingCat.ofHom b) := h
  have := Spec.map_injective h'
  exact CommRingCat.hom_ext_iff.1 this |> fun e => by simpa using e

theorem spMap_dualMap_id (Ω : Type) [Field Ω] : spMap (dualMap (RingHom.id Ω)) = 𝟙 _ := by
  have : dualMap (RingHom.id Ω) = RingHom.id _ := by
    ext a <;> simp [dualMap]
  rw [this]
  show Spec.map (CommRingCat.ofHom (RingHom.id _)) = _
  simp

theorem cst_ext {F Ω : Type} [Field F] [NumberField F] [Field Ω] {a b : F →+* Ω}
    (h : a.comp (algebraMap (𝓞 F) F) = b.comp (algebraMap (𝓞 F) F)) : a = b :=
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 F)) h

theorem exists_cover : _root_.GlobalTheory.CompanionTheory.Ar.Top.Given → Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Tor.Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (R : Top.RootModel (CMType H) (D.p + D.q)) (o : RootOrigin Y ∅ R Fx) (S : Finset ℕ), (∀ p ∈ S, p.Prime) → (∀ p : ℕ, p.Prime → (p : ℤ) ∣ discr E → p ∈ S) → o.Fl.deg = 1 → ∃ (Ω : Type) (_ : Field Ω) (_ : CharZero Ω) (K : Type) (_ : Fintype K) (J : K → Type) (_ : ∀ k, Fintype (J k)) (y : (Σ k, J k) → Ω) (bk : R.K → K) (bx : ∀ k, R.ι k ≃ J (bk k)) (i : R.Ω →+* Ω) (𝔐 : HodgeCpt Y S y) (h : 𝔐.X ⟶ o.𝔐.X) (Fl : 𝔐.Flag) (xdeg : RootIx D → K → ℤ) (e : RootIx D → Ω), Function.Injective bk ∧ (∀ k a, y ⟨bk k, bx k a⟩ = i (R.y ⟨k, a⟩)) ∧ GlobalTheory.CompanionTheory.Ar.Dominates 𝔐.ξ o.𝔐.ξ h i ∧ 𝔐.f = h ≫ o.𝔐.f ∧ 𝔐.cst = i.comp o.𝔐.cst ∧ (∀ s a, (𝔐.M.pt (Fl.b s a)).left ≫ 𝔐.m.φ = spMap (dualMap i) ≫ (o.𝔐.M.pt (o.Fl.b s a)).left ≫ o.𝔐.m.φ) ∧ (letI := i.toAlgebra; Module.finrank R.Ω Ω = Fl.deg) ∧ Fl.RootLines xdeg e ∧ 𝔐.OmVB ∧ SmoothGenericFibreM y ∧ ∀ p ∈ S, 𝔐.R p = 4 := by
  intro hG hW E _ _ _ H D l Xo c Y Sys Fx R o S hSp hSd hdeg
  have hRes : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement := hG.2.2.2.2.1
  have : CharZero R.Ω := charZero_of_injective_ringHom o.𝔐.cst.injective
  have hgen₀ := _root_.GlobalTheory.CompanionTheory.Ar.GenPtModel.genPt_mem_genericPoints E H D l Xo c Y o.𝔐.Ω₀ o.𝔐.ξ₀ o.𝔐.gen₀
  have hgen : GlobalTheory.CompanionTheory.Ar.genPt (o.𝔐.ξ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    have e : o.𝔐.ξ ≫ o.𝔐.f = Spec.map (CommRingCat.ofHom o.𝔐.fn) ≫ o.𝔐.ξ₀ := o.𝔐.fn_over
    rw [e, genPt_comp]; exact hgen₀
  obtain ⟨Ω, _, _, i, hfin, htors, hroot⟩ := GlobalTheory.T.exists_finite_extension_primes E H D l Xo c Y R.Ω (o.𝔐.ξ ≫ o.𝔐.f) S hgen hSp
  obtain ⟨K₁, _, J₁, _, y₁, bk₁, bx₁, M₁, h₁, hbk₁, hy₁, hdom₁, hnorm₁, hsm₁⟩ :=
    GlobalTheory.T.coords_after_finite_extension hRes R.K R.ι R.Ω Ω i R.y o.𝔐.X o.𝔐.ξ hfin o.𝔐.all o.𝔐.tie
  have hξ₁ : M₁.ξ ≫ h₁ ≫ o.𝔐.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
    have e : M₁.ξ ≫ h₁ = Spec.map (CommRingCat.ofHom i) ≫ o.𝔐.ξ := hdom₁
    rw [← Category.assoc, e, Category.assoc]
  have hgen₁ : GlobalTheory.CompanionTheory.Ar.genPt (M₁.ξ ≫ h₁ ≫ o.𝔐.f) ∈ genericPoints Y.X := by
    rw [hξ₁]; show GlobalTheory.CompanionTheory.Ar.genPt (Spec.map (CommRingCat.ofHom i) ≫ _) ∈ _
    rw [genPt_comp]; exact hgen
  obtain ⟨y₀, hy₀⟩ := _root_.GlobalTheory.CompanionTheory.Ar.ChangeGeo.exists_factor_XF_of_genericPoint E H D l Xo c Y Ω (M₁.ξ ≫ h₁ ≫ o.𝔐.f) hgen₁
  obtain ⟨K₂, _, J₂, _, y₂, bk₂, bx₂, B, g, hbk₂, hy₂, hdom₂, hf₂, hR₂, hfree₂, hiso₂⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.TopHodge.exists_hodgeCpt_htFree hW E H D l Xo c Y S (fun _ => 4) Ω K₁ J₁ y₁ M₁ (h₁ ≫ o.𝔐.f) y₀ hnorm₁ hy₀ hgen₁ hSp hSd
      (fun _ _ => le_rfl) (fun p hp => by rw [hξ₁]; exact htors p hp) hroot
  have hgB : B.ξ ≫ g = M₁.ξ := by
    have e : B.ξ ≫ g = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ M₁.ξ := hdom₂
    rw [e]; simp
  have hdomB : GlobalTheory.CompanionTheory.Ar.Dominates B.ξ o.𝔐.ξ (g ≫ h₁) i := by
    show B.ξ ≫ g ≫ h₁ = _
    rw [← Category.assoc, hgB]; exact hdom₁
  have hfB : B.f = (g ≫ h₁) ≫ o.𝔐.f := by rw [hf₂, Category.assoc]
  have hBξ : B.ξ ≫ B.f = y₀ ≫ Y.j := by
    rw [hf₂, ← Category.assoc, hgB]; exact hy₀
  have hcst : B.cst = i.comp o.𝔐.cst := by
    have h1 := B.cst_over
    have h2 := o.𝔐.cst_over
    have h3 : B.ξ ≫ B.f = spMap i ≫ o.𝔐.ξ ≫ o.𝔐.f := by
      rw [hf₂, ← Category.assoc, hgB]; exact hξ₁
    have h4 : spMap (B.cst.comp (algebraMap (𝓞 c.F) c.F)) =
        spMap ((i.comp o.𝔐.cst).comp (algebraMap (𝓞 c.F) c.F)) := by
      rw [← h1, ← Category.assoc, h3, RingHom.comp_assoc, spMap_comp', ← h2]
      simp
    have := c.fin
    have : NumberField c.F := {}
    exact cst_ext (spMap_inj h4)
  obtain ⟨jA, hext, hpt, hact, hlat⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.CoverLie.main E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 B i (g ≫ h₁) hdomB hfB
  obtain ⟨Li₀, _, _, M₀, j, V₀, hspan, hj, hV, hflag⟩ :=
    GlobalTheory.T.hodge_comp_comparison_middle E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hfin hdomB hfB hcst hext hpt hact
  have hvb := _root_.GlobalTheory.CompanionTheory.Ar.VbGen.isFlagVBOn_genFib E H D l Xo c Y ∅ S R.Ω Ω R.K R.ι R.y K₂ J₂ y₂ o.𝔐 o.Fl B i (g ≫ h₁) jA hdomB hfB hcst hext hpt hact hlat
  obtain ⟨K₃, _, J₃, _, y₃, bk₃, bx₃, 𝔐, g', Fl, xdeg, e, hbk₃, hy₃, hdom₃, hf₃, hR₃, hc₃, hfree₃, hFd, hFb, hlines, -, hiso₃⟩ :=
    GlobalTheory.T.hodge_cpt_label_bases hW E H D l Xo c Y S Ω K₂ J₂ y₂ B y₀ (fun s a => jA (o.Fl.b s a)) Li₀ _ _ M₀ j V₀ _ hBξ hSd hfree₂
      (fun p hp => by rw [hR₂]; exact hroot p hp) hspan hj hV hflag
  have hsm₂ : SmoothGenericFibreM y₂ :=
    _root_.GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt Ω K₁ J₁ y₁ K₂ J₂ y₂ M₁.X B.X M₁.ξ B.ξ g M₁.all B.all M₁.tie B.tie hdom₂ hsm₁ hiso₂
  have hsm₃ : SmoothGenericFibreM y₃ :=
    _root_.GlobalTheory.CompanionTheory.Ar.SmoothChange.smoothGenericFibreM_of_isoAt Ω K₂ J₂ y₂ K₃ J₃ y₃ B.X 𝔐.X B.ξ 𝔐.ξ g' B.all 𝔐.all B.tie 𝔐.tie hdom₃ hsm₂
      (fun q hq => hiso₃ q hq (hvb q hq))
  have hg' : 𝔐.ξ ≫ g' = B.ξ := by
    have e : 𝔐.ξ ≫ g' = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ B.ξ := hdom₃
    rw [e]; simp
  refine ⟨Ω, inferInstance, inferInstance, K₃, inferInstance, J₃, inferInstance, y₃, fun k => bk₃ (bk₂ (bk₁ k)),
    fun k => (bx₁ k).trans ((bx₂ _).trans (bx₃ _)), i, 𝔐, g' ≫ g ≫ h₁, Fl, xdeg, e,
    hbk₃.comp (hbk₂.comp hbk₁), ?_, ?_, ?_, ?_, ?_, ?_, hlines, ?_, hsm₃, ?_⟩
  · intro k a
    simp only [Equiv.trans_apply]
    rw [hy₃, hy₂, hy₁]
  · show 𝔐.ξ ≫ g' ≫ g ≫ h₁ = _
    rw [← Category.assoc, hg']; exact hdomB
  · rw [hf₃, hf₂]; simp
  · rw [hc₃, hcst]
  · intro s a
    rw [hFb, hpt, spMap_dualMap_id, Category.id_comp]
  · rw [hFd, hdeg, _root_.mul_one]
  · intro p hp
    have := hfree₃ p hp
    exact this
  · intro p hp
    rw [hR₃, hR₂]

end GlobalTheory.CompanionTheory.Ar.ChangeGeo
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ToroidalFlagSmoothProjective
section
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj GlobalTheory.CompHS

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.FlagSmooth

open TopologicalSpace _root_.CategoryTheory.Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Reg GlobalTheory.FlagEmb GlobalTheory.ProjSpace GlobalTheory.FlagMod
  GlobalTheory.FlagMod.FieldFlag
open GlobalTheory.FlagMod.LowRank (ECh Proj str)
open MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_gChart_of_flagCover {Y : Model Xo c (RingHom.id c.F)} (X : FlagCover Y) (x : Y.X) :
    ∃ M : GChart Y, x ∈ M.U := by
  obtain ⟨z, rfl⟩ := GlobalTheory.BaseVar.surjective_π X x
  have hz : z ∈ (⨆ k, X.F.U k) := by rw [X.F.cover]; trivial
  obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hz
  exact ⟨X.F.M k, X.F.le k hk⟩

theorem nonempty_atlas_of_cover (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F))
    (hG : ∀ x : Y.X, ∃ M : GChart Y, x ∈ M.U) : Nonempty (Atlas Y p) := by
  classical
  have : IsProper Y.s := projProper _ _ _ Y.proj
  have : IsReduced Y.X := by
    have : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      have := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  obtain ⟨L, N, σ, A, C, haff, hle, hCA, htw⟩ := GlobalTheory.TwistEmb.exists_twist_embedding c.F Y.X Y.s (GChart Y)
    (fun j => j.U) (fun j => j.n) (fun j j' => chg j.toMChart j'.toMChart) Y.proj
    (fun x => hG x)
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

theorem exists_cellModel (Y : Model Xo c (RingHom.id c.F)) (p : Proj (RingHom.id c.F)) (A : Atlas Y p) :
    ∃ (M : FlagModel Y) (g : ∀ en : En Dw.mult, M.YY ⟶ PSpace c.F (plN A.N en.1))
      (κ : ∀ b, Pm Dw.mult → (Sp (CR Dw.mult (A.V b)) ⟶ M.YY)) (_ : ∀ b w, IsOpenImmersion (κ b w)),
      Cells A M.π g κ := by
  have := A.fin
  obtain ⟨Z, π, g, κ, h1, h2, h3, h4, h5, h6⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_properFlag c.F Y.X Y.s (E →+* ℂ) Dw.mult A.N A.B A.V A.alpha A.cv
    A.Dv Y.proj Y.normal (_root_.GlobalTheory.FlagMod.FieldFlag.atlas_isCover E H Dw l Xo c Y p A) A.cov
  have hZ : Cells A π g κ := ⟨h1, h2, h3, h5, h6⟩
  have := h4
  have ht := _root_.GlobalTheory.FlagMod.FieldFlag.flagCells_frames_triangular E H Dw l Xo c Y p A Z π g κ hZ
  have huniq : ∀ (S' : Type) [CommRing S'] [Algebra c.F S'] (P₁ : FrPt Xo c S') (z₁ z₂ : Sp S' ⟶ Z),
      (cellFrames hZ ht).Lies z₁ P₁ → (cellFrames hZ ht).Lies z₂ P₁ → z₁ = z₂ := by
    intro S' _ _ P₁ z₁ z₂ e₁ e₂
    refine _root_.GlobalTheory.FlagMod.FieldFlag.hom_ext_of_localization_atPrime S' Z z₁ z₂ fun q => ?_
    obtain ⟨P', hP'⟩ := exists_frMap (IsScalarTower.toAlgHom c.F S' (Localization.AtPrime q.asIdeal)) P₁
    have l₁ := e₁.frMap hP'
    have l₂ := e₂.frMap hP'
    refine _root_.GlobalTheory.FlagMod.FieldFlag.cell_sep E H Dw l Xo c Y p A Z π g κ hZ ht _ _ _ _ l₁.1 l₂.1 fun σ i => ?_
    obtain ⟨k, hk⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover
      (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₁)
    obtain ⟨k', hk'⟩ := exists_chart_of_isLocalRing (cellFrames hZ ht).cover
      (spMap (algebraMap S' (Localization.AtPrime q.asIdeal)) ≫ z₂)
    exact (l₁.initSpan_eq hk l₁.1 rfl σ i).symm.trans (l₂.initSpan_eq hk' l₂.1 rfl σ i)
  refine ⟨{ YY := Z, π := π, proper := h1, normal := h2, flat := ?_, F := cellFrames hZ ht
            dense := _root_.GlobalTheory.FlagMod.FieldFlag.dense_genMap_preimage E H Dw l Xo c Y p A Z π g κ hZ, top := _root_.GlobalTheory.FlagMod.FieldFlag.cellFrames_topEigen E H Dw l Xo c Y p A Z π g κ hZ ht
            rep := fun S _ _ P => ?_, fin := fun K _ _ z => ?_ }, g, κ, h4, hZ⟩
  · exact _root_.GlobalTheory.flat_to_spec_field c.F Z (π ≫ Y.s)
  · obtain ⟨z, hz⟩ := _root_.GlobalTheory.FlagMod.FieldFlag.exists_lies_of_local E H Dw l Xo c Y p A Z π g κ hZ ht S P huniq fun q =>
      _root_.GlobalTheory.FlagMod.FieldFlag.exists_cell_lies E H Dw l Xo c Y p A Z π g κ hZ ht S P q
    exact ⟨z, hz, fun z' hz' => huniq S P z' z hz' hz⟩
  · refine (Set.finite_singleton z).subset fun z' ⟨hx, h⟩ => ?_
    exact _root_.GlobalTheory.FlagMod.FieldFlag.cell_sep E H Dw l Xo c Y p A Z π g κ hZ ht K z' z _ hx rfl h

theorem smooth_proj_flagStr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (T : GlobalTheory.CompHS.TorFlag Xo c), ∃ d : ℕ, SmoothOfRelativeDimension d (GlobalTheory.CompHS.flagStr T.X) ∧ IsProjOver (GlobalTheory.CompHS.flagStr T.X) := by
  intro E _ _ _ H D l Xo c T
  obtain ⟨p⟩ := GlobalTheory.FlagMod.LowRank.nonempty_proj_id (E := E) (c := c)
  obtain ⟨A⟩ := nonempty_atlas_of_cover T.Y p (exists_gChart_of_flagCover T.X)
  obtain ⟨M, g, κ, hκ, hZ⟩ := exists_cellModel T.Y p A
  obtain ⟨d, hsm, hpr⟩ := _root_.GlobalTheory.CompanionTheory.FlagMod.cells_smooth_proj E H D l Xo c T.Y p A M.YY M.π g κ hκ hZ T.smooth
  obtain ⟨h, hh, hπ⟩ := _root_.GlobalTheory.CompanionTheory.FlagMod.flagModel_iso_cells E H D l Xo c T.Y p A M g κ hκ hZ T.smooth T.flag
  have e : flagStr T.X = h ≫ M.π ≫ T.Y.s := by
    rw [← Category.assoc, hπ]
  refine ⟨d, ?_, ?_⟩
  · rw [e]; exact GlobalTheory.VarFlag.smooth_iso h _ hsm
  · rw [e]
    obtain ⟨N, i, hi, hs⟩ := hpr
    exact ⟨N, h ≫ i, inferInstance, by rw [Category.assoc, hs]⟩

end GlobalTheory.CompanionTheory.FlagSmooth
end
end

