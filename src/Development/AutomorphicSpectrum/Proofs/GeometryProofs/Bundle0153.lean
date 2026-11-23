module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0005
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.HodgeGramComplexConjugate
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0141
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0148
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0103
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
public import Development.AutomorphicSpectrum.Statements.GeometryStatements.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AddJFintype
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenericCoordsDescendSubfield
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0022
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0092
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0102
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0149
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0133
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0097
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0105
public import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenLatticeVectorBundle
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0146

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeGramConjugate
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem isHodgeGram_conj : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (x x' : Sp ℂ ⟶ S) (k : ℕ) (v : Fin k → (epsAt x ⟶ G)) (v' : Fin k → (epsAt x' ⟶ G)) (Γ : Matrix (Fin k) (Fin k) ℂ), x' = spMap (starRingEnd ℂ) ≫ x → (∀ a, (v' a).left = spMap (dualMap (starRingEnd ℂ)) ≫ (v a).left) → IsHodgeGram G L x v Γ → IsHodgeGram G L x' v' (Γ.map star) := by
  exact @PositivityTheory.Xgn.hodge_gram_complex_conjugate_alt

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionAt
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

theorem spec_dual_fst {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) :
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom B B B).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (dualMap φ)) =
      Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
  simp [dualMap]

theorem tan_of_lieVal {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {G : Over X} [GrpObj G]
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {M : LieModel G ξ Li} {z : Sp ℂ ⟶ X} {e : Li}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : IsTanAt G z w := by
  obtain ⟨hz, v, ⟨hv, -⟩, hw⟩ := h
  unfold IsTanAt at hv ⊢
  let t : Over.mk z ⟶ Over.mk (X.fromSpecStalk (centre z)) :=
    Over.homMk (Spec.map (Scheme.stalkClosedPointTo z)) (Scheme.Spec_stalkClosedPointTo_fromSpecStalk z)
  have h1 : t ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) = 1 := MonObj.comp_one t
  have h2 := congrArg CommaMorphism.left h1
  rw [hw]
  refine Eq.trans ?_ h2
  change _ = Spec.map (Scheme.stalkClosedPointTo z) ≫ (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G).left
  refine Eq.trans ?_ (congrArg (fun k => Spec.map (Scheme.stalkClosedPointTo z) ≫ k) hv)
  have key := spec_dual_fst (Scheme.stalkClosedPointTo z).hom
  exact (Category.assoc _ _ _).symm.trans ((congrArg (fun k => k ≫ v.left) key).trans (Category.assoc _ _ _))

theorem eq_sum_of_mem_flagStep {Ω : Type} [Field Ω] {Li : Type} [AddCommGroup Li] [Module Ω Li] {r n : ℕ}
    (hn : n ≤ r) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li) (hd : ∀ j l, π j (b l) = if j = l then 1 else 0)
    {w : Li} (hw : w ∈ flagStep Ω b n) :
    w = ∑ l : Fin n, π (Fin.castLE hn l) w • b (Fin.castLE hn l) := by
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    have hk' : (k : ℕ) < n := hk
    rw [Finset.sum_eq_single (⟨k, hk'⟩ : Fin n)]
    · simp [hd, Fin.castLE]
    · intro l _ hl
      have : Fin.castLE hn l ≠ k := fun e => hl (Fin.ext (by simpa using congrArg Fin.val e))
      simp [hd, this]
    · simp
  | zero => simp
  | add x y _ _ hx hy =>
    conv_lhs => rw [hx, hy]
    simp [add_smul, Finset.sum_add_distrib]
  | smul a x _ hx =>
    conv_lhs => rw [hx]
    simp [Finset.smul_sum, mul_smul]

theorem ev_sum {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {z : Sp ℂ ⟶ X} {p : Cpt ξ}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Submodule (regAt ξ p) Li} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ev : L →+ V)
    (hev : ∀ (a : regAt ξ p) (r : ℂ) e, ValAt ξ z (a : Ω) r → ev (a • e) = r • ev e) {n : ℕ} (g : Fin n → Li)
    (hg : ∀ l, g l ∈ L) (a : Fin n → Ω) (ha : ∀ l, a l ∈ regAt ξ p) (c : Fin n → ℂ)
    (hc : ∀ l, ValAt ξ z (a l) (c l)) {w : Li} (hw : w ∈ L) (hwe : w = ∑ l, a l • g l) :
    ev ⟨w, hw⟩ = ∑ l, c l • ev ⟨g l, hg l⟩ := by
  have h1 : (⟨w, hw⟩ : L) = ∑ l, (⟨a l, ha l⟩ : regAt ξ p) • (⟨g l, hg l⟩ : L) := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact hwe
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  exact Finset.sum_congr rfl fun l _ => hev _ _ _ (hc l)

theorem gram_val : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)) (i : Fin r), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (s : ℂ),
      (∀ j, f j ∈ flagStep Ω b i) → e ∈ flagStep Ω b (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      ValAt ξ z (π i e) s → s ≠ 0 → (gramAt h z v).det ≠ 0 →
      (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ -
          Real.log ‖(gramAt h z v).det‖) =
        Real.log ‖s‖ + (1 / 2) * (Real.log ‖(gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det‖ -
          Real.log ‖(gramAt h z fun l : Fin i => B (Fin.castLE i.2.le l)).det‖) := by
  intro X Ω _ ξ K J y G _ _ _ Li _ _ M h z hz r b π B i hξ hd hreg hB f e v ve s hf he hv hve hs hs0 hdet
  obtain ⟨Vz, _, _, ⟨MR⟩⟩ := lieModel_exists X G ℂ z
  obtain ⟨ev, hev1, hev2, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val X G Ω ξ Li M ℂ z hz Vz MR hξ inferInstance
  obtain ⟨core, hcore⟩ := h.herm z Vz MR
  have val : ∀ {e' : Li} {w : epsAt z ⟶ G}, M.ValAt z e' w →
      ∃ he' : e' ∈ M.lat ⟨centre z, hz⟩, MR.pt (ev ⟨e', he'⟩) = w := by
    intro e' w hw
    obtain ⟨x, rfl⟩ := MR.onto w (tan_of_lieVal hw)
    obtain ⟨he', hx⟩ := (hev1 e' x).1 hw
    exact ⟨he', by rw [hx]⟩
  choose hbL hbB using fun j => val (hB j)
  choose hfL hfv using fun j => val (hv j)
  obtain ⟨heL, hve'⟩ := val hve
  obtain ⟨β, hβ⟩ : ∃ β : Fin (i + 1) → Vz, ∀ l, β l = ev ⟨b (Fin.castLE i.2 l), hbL _⟩ := ⟨_, fun _ => rfl⟩
  obtain ⟨x, hx⟩ : ∃ x : Fin i → Vz, ∀ j, x j = ev ⟨f j, hfL j⟩ := ⟨_, fun _ => rfl⟩
  obtain ⟨xe, hxe⟩ : ∃ xe : Vz, xe = ev ⟨e, heL⟩ := ⟨_, rfl⟩
  have hi : (i : ℕ) ≤ r := i.2.le
  have hC : ∀ (j : Fin i) (l : Fin r), ∃ c : ℂ, ValAt ξ z (π l (f j)) c :=
    fun j l => val_exists (hreg l _ (hfL j))
  choose C hC using hC
  have hD : ∀ l : Fin r, ∃ c : ℂ, ValAt ξ z (π l e) c := fun l => val_exists (hreg l _ heL)
  choose D hD using hD
  have hsD : D i = s := val_unique hξ (hD i) hs
  have hsum : ∀ j, x j = ∑ l : Fin i, C j (Fin.castLE hi l) • β l.castSucc := by
    intro j
    rw [hx j, ev_sum ev hev2 (fun l : Fin i => b (Fin.castLE hi l)) (fun _ => hbL _)
      (fun l => π (Fin.castLE hi l) (f j)) (fun _ => hreg _ _ (hfL j)) (fun l => C j (Fin.castLE hi l))
      (fun _ => hC _ _) (hfL j) (eq_sum_of_mem_flagStep hi b π hd (hf j))]
    exact Finset.sum_congr rfl fun l _ => by rw [hβ]; rfl
  have hsume : xe = ∑ l : Fin i, D (Fin.castLE hi l) • β l.castSucc + s • β (Fin.last i) := by
    rw [hxe, ev_sum ev hev2 (fun l : Fin (i + 1) => b (Fin.castLE i.2 l)) (fun _ => hbL _)
      (fun l => π (Fin.castLE i.2 l) e) (fun _ => hreg _ _ heL) (fun l => D (Fin.castLE i.2 l))
      (fun _ => hD _) heL (eq_sum_of_mem_flagStep i.2 b π hd he), Fin.sum_univ_castSucc]
    congr 1
    · exact Finset.sum_congr rfl fun l _ => by rw [hβ]; rfl
    · rw [hβ, ← hsD]; rfl
  have gr : ∀ {m : ℕ} (u : Fin m → Vz),
      gramAt h z (fun l => MR.pt (u l)) = Matrix.of fun a b => core.inner (u a) (u b) := by
    intro m u
    ext a c
    simp [gramAt, hcore]
  have e1 : v = fun l => MR.pt (x l) := funext fun j => by rw [hx, hfv]
  have e2 : (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G)) =
      fun l => MR.pt ((Fin.snoc x xe : Fin (i + 1) → Vz) l) := by
    funext l
    refine Fin.lastCases ?_ (fun l => ?_) l
    · simp [hxe, hve']
    · simp [e1]
  have e3 : (fun l : Fin (i + 1) => B (Fin.castLE i.2 l)) = fun l => MR.pt (β l) :=
    funext fun l => by rw [hβ, hbB]
  have e4 : (fun l : Fin i => B (Fin.castLE i.2.le l)) = fun l => MR.pt (β l.castSucc) :=
    funext fun l => by rw [hβ, hbB]; rfl
  have hind := _root_.GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gramAt_det_ne_zero X Ω ξ K J y G Li M h z hz r b π B hξ hd hreg hB (i + 1) (Fin.castLE i.2)
    (Fin.castLE_injective _)
  change (gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det ≠ 0 at hind
  rw [e3, gr] at hind
  rw [e1, gr] at hdet
  rw [e2, e3, e4, e1, gr, gr, gr, gr]
  exact _root_.GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_quot Vz core i β x xe (Matrix.of fun j l => C j (Fin.castLE hi l))
    (fun l => D (Fin.castLE hi l)) s hsum hsume hs0 hdet hind

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelConstantsExtension
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagStep

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagStep

theorem mem_of_mem_iSup_of_indep {Ω W I : Type} [Field Ω] [AddCommGroup W] [Module Ω W] (A : Subring Ω)
    {F : I → Submodule Ω W} (hF : iSupIndep F) {P : I → Submodule A W}
    (hP : ∀ t, P t ≤ (F t).restrictScalars A) (s : I) {x : W} (hx : x ∈ ⨆ t, P t) (hxs : x ∈ F s) : x ∈ P s := by
  classical
  have hsplit : (⨆ t, P t) ≤ P s ⊔ ⨆ (t) (_ : t ≠ s), P t := iSup_le fun t => by
    by_cases e : t = s
    · subst e
      exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le t e le_rfl)
  obtain ⟨a, ha, d, hd, rfl⟩ := Submodule.mem_sup.1 (hsplit hx)
  have hd2 : d ∈ ⨆ (t) (_ : t ≠ s), F t := by
    have hle : (⨆ (t) (_ : t ≠ s), P t) ≤ (⨆ (t) (_ : t ≠ s), F t).restrictScalars A :=
      iSup₂_le fun t e v hv => (le_iSup₂_of_le t e le_rfl : F t ≤ ⨆ (t) (_ : t ≠ s), F t) (hP t hv)
    exact hle hd
  have hd3 : d ∈ F s := by
    have h := sub_mem hxs (show a ∈ F s from hP s ha)
    simpa using h
  have h0 : d = 0 := Submodule.disjoint_def.1 (hF s) d hd3 hd2
  rw [h0, add_zero]
  exact ha

theorem eigLat_isFlagVBOn_of_pull_char0 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Tor.Level H) (c : Coeff l)
    (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (Ω₀ Ω : Type) [Field Ω₀] [Field Ω] [CharZero Ω₀]
    [CharZero Ω] [Algebra Ω₀ Ω] (ξ : Spec (CommRingCat.of Ω₀) ⟶ X) (ξ' : Spec (CommRingCat.of Ω) ⟶ X')
    (cst : c.F →+* Ω₀) (V V' : Type) [AddCommGroup V] [Module Ω₀ V] [AddCommGroup V'] [Module Ω V']
    (M : LieModel t.G ξ V) (M' : LieModel t'.G ξ' V') (ρ : 𝓞 E →+* Module.End Ω₀ V) (ρ' : 𝓞 E →+* Module.End Ω V')
    (L : CMType H ⊕ CMType H → Lat ξ V) (j : V →+ V') (r : CMType H ⊕ CMType H → ℕ)
    (b : ∀ s, Fin (r s) → V'),
    IsCptGen ξ → IsCptGen ξ' → GlobalTheory.CompanionTheory.Ar.Dominates ξ' ξ f (algebraMap Ω₀ Ω) →
    M.IsActOf t.act.act ρ → M'.IsActOf t'.act.act ρ' →
    (∀ q : Cpt ξ, (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → IsIntegrallyClosed (regAt ξ q)) →
    (∀ q : Cpt ξ', (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) → IsIntegrallyClosed (regAt ξ' q)) →
    (∀ s (q : Cpt ξ), (∀ r : ℕ, r.Prime → ¬ InFibre ξ r q) → L s q = M.eigLat ρ (cst.comp (labelEmb c s)) q) →
    M'.lat = M.lat.pull ξ' f j →
    (∀ s, ∀ e ∈ eigSp ρ (cst.comp (labelEmb c s)),
      j e ∈ eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) →
    (∀ s, ((L s).pull ξ' f j).IsFlagVBOn Set.univ (b s)) →
    ∀ s, (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))).IsFlagVBOn
      {q | ∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q} (b s) := by
  intro E _ _ _ H l c X X' t t' f Ω₀ Ω _ _ _ _ _ ξ ξ' cst V V' _ _ _ _ M M' ρ ρ' L j r b hg hg' hd hact hact' hint hint'
    hL hlat hj hfl
  have key : ∀ s (q : Cpt ξ'), (∀ r : ℕ, r.Prime → ¬ InFibre ξ' r q) →
      (M'.eigLat ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c s))) q = ((L s).pull ξ' f j) q := by
    intro s q hq
    obtain ⟨h, -, h2⟩ := RegAtDom.regAt_dominates X Ω₀ ξ X' Ω ξ' f (algebraMap Ω₀ Ω) hd q
    have hp : ∀ r : ℕ, r.Prime → ¬ InFibre ξ r ⟨f q.1, h⟩ := fun r hr hn =>
      hn (h2 hg' _ (natCast_mem _ r) (by rw [map_natCast]; exact not_not.1 (hq r hr)))
    have hsum := (SatModel.lat_eq_iSup_of_char0 c t ξ hg cst M ρ hact hint).2 _ hp
    have hind := (SatModel.lat_eq_iSup_of_char0 c t' ξ' hg' ((algebraMap Ω₀ Ω).comp cst) M' ρ' hact' hint').1
    have hle : ∀ u, ((L u).pull ξ' f j) q ≤ M'.lat q ⊓
        (eigSp ρ' (((algebraMap Ω₀ Ω).comp cst).comp (labelEmb c u))).restrictScalars (regAt ξ' q) := by
      intro u
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he' : e ∈ M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
        have h3 := hL u ⟨f q.1, h⟩ hp
        have h4 : e ∈ L u ⟨f q.1, h⟩ := he
        rw [h3] at h4
        exact h4
      refine ⟨?_, hj u e he'.2⟩
      show j e ∈ M'.lat q
      rw [hlat]
      exact Submodule.subset_span ⟨h, e, he'.1, rfl⟩
    have hall : M'.lat q ≤ ⨆ u, ((L u).pull ξ' f j) q := by
      rw [hlat]
      refine Submodule.span_le.2 ?_
      rintro _ ⟨h', e, he, rfl⟩
      have he1 : e ∈ ⨆ u, M.lat.inter (eigSp ρ (cst.comp (labelEmb c u))) ⟨f q.1, h⟩ := by
        rw [← hsum]
        exact he
      refine Submodule.iSup_induction _ (motive := fun e => j e ∈ ⨆ u, ((L u).pull ξ' f j) q) he1
        (fun u e he => ?_) ?_ (fun x y hx hy => ?_)
      · refine Submodule.mem_iSup_of_mem u (Submodule.subset_span ⟨h, e, ?_, rfl⟩)
        have h3 := hL u ⟨f q.1, h⟩ hp
        rw [h3]
        exact he
      · simp only [map_zero]
        exact zero_mem _
      · simp only [map_add (f := _)]
        exact add_mem hx hy
    refine le_antisymm ?_ (hle s)
    rintro x ⟨hx1, hx2⟩
    exact mem_of_mem_iSup_of_indep (regAt ξ' q) hind (fun u => (hle u).trans inf_le_right) s (hall hx1) hx2
  intro s p hp
  obtain ⟨U, hU, b', hb, hf⟩ := hfl s p trivial
  refine ⟨U, hU, b', hb, fun q hq hqU => ?_⟩
  obtain ⟨h1, h2⟩ := hf q trivial hqU
  exact ⟨h1, (key s q hq).trans h2⟩

end GlobalTheory.CompanionTheory.Ar.FlagStep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.OrthogonalMetricFlagDegree
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FlagFib

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi _root_.GlobalTheory.CompanionTheory.Ar

theorem flagStep_mono' {Ω E' : Type} [Field Ω] [AddCommGroup E'] [Module Ω E'] {r : ℕ} (b : Fin r → E') {i i' : ℕ} (h : i ≤ i') :
    flagStep Ω b i ≤ flagStep Ω b i' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

theorem exists_satFlag {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
    {Li : Type} [AddCommGroup Li] [Module Ω Li] {L : Type} [Field L] [NumberField L] (M : LieModel G ξ Li)
    (z : Sp (𝓞 L) ⟶ X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel G z B.carrier) {r : ℕ}
    (b : Fin r → Li) (hr : ∀ i : ℕ, i ≤ r → Module.finrank (𝓞 L) (subFib M (flagStep Ω b i) z MB) = i) :
    ∃ A : SatFlag B r, ∀ i, A.F i = subFib M (flagStep Ω b i.val) z MB :=
  ⟨{ F := fun i => subFib M (flagStep Ω b i.val) z MB
     mono := fun _ _ hi => subFib_mono M (flagStep_mono' b (Fin.le_def.1 hi)) z MB
     sat := fun _ => subFib_saturated M _ z B MB
     rank := fun i => hr i.val (Nat.lt_succ_iff.1 i.2) }, fun _ => rfl⟩

theorem rank_fib : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier),
    Fintype.card (CMType H) * (D.p + D.q) = Module.finrank (𝓞 L) B.carrier ∧
    (∀ s (i : ℕ), i ≤ labelRk D s → Module.finrank (𝓞 L) (subFib 𝔐.M (flagStep Ω (Fl.b s) i) z MB) = i) ∧
    ∀ s (i : ℕ), flagStep Ω (Fl.b s) i ≤ 𝔐.Vgen s := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J y 𝔐 _ Fl L _ _ z B MB
  classical
  have hgen : IsCptGen 𝔐.ξ := 𝔐.tie.gen
  haveI hsm : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hs : genPt 𝔐.ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z) := 𝔐.all _
  have hu := fun n hn => isUnit_natCast_stalk 𝔐.X L (spMap (algebraMap (𝓞 L) L) ≫ z) n hn
  obtain ⟨b, hb1, hb2, hb3, hb4, hb5, hb6⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagFrames.exists_frames E H D l Xo c Y S Ω K J y 𝔐 Fl ⟨_, hs⟩ hu
  obtain ⟨T, _, _, _, _, TL, j, hj, hbc⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_liftBaseChange 𝔐.X 𝔐.t.G (𝓞 L) L z B.carrier MB
  obtain ⟨w, hw1, hw2, hw3, hw4⟩ := _root_.GlobalTheory.CompanionTheory.Ar.FlagFib.lieModel_valFrame 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L _ T TL hs
    (Σ s, Fin (labelRk D s)) _ hgen hb3 hb4 hb5
  have hbr := fun U => _root_.GlobalTheory.CompanionTheory.Ar.FlagFib.Bridge.finrank_subFib 𝔐.X 𝔐.t.G Ω 𝔐.ξ 𝔐.Li 𝔐.M L z B.carrier MB T TL j U hgen hj hbc
  refine ⟨?_, ?_, ?_⟩
  · rw [(hbr ⊥).1]
    have e1 := finrank_span_eq_card hw2
    rw [hw3, finrank_top] at e1
    rw [e1, Fintype.card_sigma, Fintype.sum_sum_type]
    have a1 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inl τ))) = D.p := fun _ => Fintype.card_fin _
    have a2 : ∀ τ : CMType H, Fintype.card (Fin (labelRk D (Sum.inr τ))) = D.q := fun _ => Fintype.card_fin _
    simp only [a1, a2, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    ring
  · intro s i hi
    rw [(hbr _).2]
    let g : Fin i → Σ s, Fin (labelRk D s) := fun k => ⟨s, ⟨k.1, lt_of_lt_of_le k.2 hi⟩⟩
    have hg : Function.Injective g := by
      intro a b' hab
      simp only [g, Sigma.mk.injEq, heq_eq_eq, true_and, Fin.mk.injEq] at hab
      exact Fin.ext hab
    have himg : (fun q : Σ s, Fin (labelRk D s) => b q.1 q.2) '' Set.range g = b s '' {k | (k : ℕ) < i} := by
      ext x
      constructor
      · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
        exact ⟨⟨k.1, lt_of_lt_of_le k.2 hi⟩, k.2, rfl⟩
      · rintro ⟨k, hk, rfl⟩
        exact ⟨_, ⟨⟨k.1, hk⟩, rfl⟩, rfl⟩
    have hspan : Submodule.span L {w' | ∃ e ∈ flagStep Ω (Fl.b s) i, 𝔐.M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e (TL.pt w')} =
        Submodule.span L (Set.range (w ∘ g)) := by
      apply le_antisymm
      · refine Submodule.span_le.2 ?_
        rintro w' ⟨e, he, hv⟩
        obtain ⟨h', hl⟩ := (LieModel.exists_valAt_iff 𝔐.M _ e).1 ⟨_, hv⟩
        have h2 := hb2 s i e (by rw [hb1]; exact he) hl
        rw [← himg] at h2
        have := hw4 (Set.range g) e w' h2 hv
        rwa [← Set.range_comp] at this
      · refine Submodule.span_le.2 ?_
        rintro _ ⟨k, rfl⟩
        refine Submodule.subset_span ⟨b s ⟨k.1, lt_of_lt_of_le k.2 hi⟩, ?_, hw1 (g k)⟩
        rw [← hb1]
        exact Submodule.subset_span ⟨_, k.2, rfl⟩
    rw [hspan, finrank_span_eq_card (hw2.comp g hg), Fintype.card_fin]
  · intro s i
    rw [← hb1, ← hb6]
    exact Submodule.span_mono (Set.image_subset_range _ _)

theorem flag_fibre : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) [Fintype (CMType H)] (Fl : 𝔐.Flag) (h : LieMetric 𝔐.M y), h.Orth 𝔐.t.act → ∀ (L : Type) [Field L] [NumberField L] (z : Sp (𝓞 L) ⟶ 𝔐.X) (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (MB : LieModel 𝔐.t.G z B.carrier), IsFibre (fun z v w c => c = h.ip z v w) z B MB → ∃ (A : FlagPair B (CMType H) D.p D.q), A.IsOrthFull ∧ (∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A.W τ).F i)) ∧ ∀ τ i, IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A.S τ).F i) := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐 _ Fl h hO L _ _ z B MB hF
  obtain ⟨h1, h2, h3⟩ := rank_fib E H D l Xo c Y S Ω K J y 𝔐 Fl L z B MB
  have ho := _root_.GlobalTheory.CompanionTheory.Ar.FlagFib.FibOrth.orthAt_subFib E H D l Xo c Y S Ω K J y 𝔐 h hO L z B MB hF
  have hex : ∀ s, ∃ A : SatFlag B (labelRk D s), ∀ i, A.F i = subFib 𝔐.M (flagStep Ω (Fl.b s) i.val) z MB := by
    intro s
    exact exists_satFlag 𝔐.M z B MB (Fl.b s) (h2 s)
  choose A hA using hex
  have hW : ∀ (τ : CMType H) (i : Fin (D.p + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inl τ)) i.val) z MB ((A (.inl τ)).F i) := by
    intro τ i
    rw [hA (.inl τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hS : ∀ (τ : CMType H) (i : Fin (D.q + 1)), IsSubFibre 𝔐.M (flagStep Ω (Fl.b (.inr τ)) i.val) z MB ((A (.inr τ)).F i) := by
    intro τ i
    rw [hA (.inr τ) i]
    exact isSubFibre_subFib _ _ _ _
  have hpart : ∀ s, FlagPair.part (⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩ : FlagPair B (CMType H) D.p D.q) s =
      subFib 𝔐.M (flagStep Ω (Fl.b s) (labelRk D s)) z MB := by
    rintro (τ | τ)
    · exact hA (.inl τ) (Fin.last _)
    · exact hA (.inr τ) (Fin.last _)
  refine ⟨⟨fun τ => A (.inl τ), fun τ => A (.inr τ)⟩, ⟨?_, h1⟩, hW, hS⟩
  intro a b hab
  rw [hpart, hpart]
  exact ho a b hab _ _ (h3 a _) (h3 b _)

end GlobalTheory.CompanionTheory.Ar.FlagFib
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.PointFrameSpecialization
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.FrameVal

theorem exists_framed_values : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β) (U : Set (Xo.XF c)) (Z : CptOver Y U) (τ : E →+* ℂ) (σ : c.F →+* ℂ) (b₁ : Fin D.p → Z.V) (b₂ : Fin D.q → Z.V) (y : Sp ℂ ⟶ Xo.XF c) (h : genPt (Z.ξ₀ ≫ Y.j) ⤳ centre (y ≫ Y.j)), (Function.Injective β ∧ IsNoetherianRing O ∧ ∀ x : c.F, ∃ a b : O, β b ≠ 0 ∧ x * β b = β a) → τ (H.rt : E) = H.rt0 → σ (tauIn c τ H.rt) = H.rt0 → y ≫ pullback.snd _ _ = spMap σ → (Z.eig τ).IsFrameAt b₁ ⟨_, h⟩ → (Z.eig (ComplexEmbedding.conjugate τ)).IsFrameAt b₂ ⟨_, h⟩ → ∃ (v : Vecs y D.p) (w : Vecs y D.q), IsFramed Set.univ τ σ y v w ∧ (∀ i, ∃ v', Z.M.ValAt (y ≫ Y.j) (b₁ i) v' ∧ SameVec Y y (v i) v') ∧ ∀ j, ∃ w', Z.M.ValAt (y ≫ Y.j) (b₂ j) w' ∧ SameVec Y y (w j) w' := by
  intro E _ _ _ H D l Xo c O _ β Y U Z τ σ b₁ b₂ y h hO hτ _ hy hf₁ hf₂
  haveI : Smooth Y.t.G.hom := Y.t.semi.smooth
  obtain ⟨-, -, h3, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Flat.isVBOn_eig_genFib E H D l Xo c O β Y U Z τ hO hτ
  have hfib : (⟨centre (y ≫ Y.j), h⟩ : Cpt (Z.ξ₀ ≫ Y.j)) ∈ Z.genFib :=
    ⟨Y.jQ (y (IsLocalRing.closedPoint ℂ)), by simp only [Model.j, centre, Scheme.Hom.comp_apply]⟩
  obtain ⟨g, b, hb, hS⟩ := h3 _ hfib
  obtain ⟨ER, _, _, ⟨MR⟩⟩ := lieModel_exists Y.X Y.t.G ℂ (y ≫ Y.j)
  obtain ⟨ev, hev, -, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieLat_val Y.X Y.t.G Z.Ω (Z.ξ₀ ≫ Y.j) Z.V Z.M ℂ (y ≫ Y.j) h ER MR Z.gen inferInstance
  have hval : ∀ {n : ℕ} (τ' : E →+* ℂ) (e : Fin n → Z.V), (Z.eig τ').IsFrameAt e ⟨centre (y ≫ Y.j), h⟩ →
      ∀ i, ∃ w, Z.M.ValAt (y ≫ Y.j) (e i) (MR.pt w) := fun τ' e hf i => by
    have hmem : e i ∈ Z.eig τ' ⟨centre (y ≫ Y.j), h⟩ := by
      rw [hf.2]
      exact Submodule.subset_span ⟨i, rfl⟩
    exact ⟨ev ⟨e i, hmem.1⟩, (hev _ _).2 ⟨hmem.1, rfl⟩⟩
  choose w₁ hw₁ using hval τ b₁ hf₁
  choose w₂ hw₂ using hval _ b₂ hf₂
  choose v hv using fun i => exists_sameVec_left Y y (MR.pt (w₁ i))
  choose w hw using fun j => exists_sameVec_left Y y (MR.pt (w₂ j))
  obtain ⟨hL₁, hL₂⟩ := GlobalTheory.CompanionTheory.Ar.LocFrames.lieMult_at y σ τ hy hτ
  refine ⟨v, w, ⟨hy, Set.subset_univ _, ?_, ?_⟩, fun i => ⟨_, hw₁ i, hv i⟩, fun j => ⟨_, hw₂ j, hw j⟩⟩
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y τ D.p b₁ v (fun i => MR.pt (w₁ i)) h hO.2.2 hy hL₁
      ⟨g, b, hb, hS τ⟩ hf₁ hw₁ hv
  · exact GlobalTheory.CompanionTheory.Ar.LocFrames.isEigFrame_of_values Z σ y _ D.q b₂ w (fun j => MR.pt (w₂ j)) h hO.2.2 hy hL₂
      ⟨g, b, hb, hS _⟩ hf₂ hw₂ hw

end GlobalTheory.CompanionTheory.Ar.FrameVal
end
end

