module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0075
public import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
public import Formalism.SharpRestriction.Divisibility.OrbitPlaces
public import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0068
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.FirstKernelLawReading
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
public import Formalism.LocalToGlobal.Columns.Bundle0005
public import Formalism.SharpRestriction.GrowthBounds.WeilJacquetShalikaLaw
public import Formalism.SharpRestriction.ParConsts
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsPlaceCofactorValuationLowerBound
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0072
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0010
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.ExistsCoprimePowEqOne
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0076
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.FrobeniusOrbits.HostCorollaries
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
public import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.CrystallineAtPlaces

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrrDistinctConstituentsAfterExtension
section
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory

theorem absIrrDistinct_repK_of_oSplitAt_of_mapRep_distinct : ∀ (D : D7) (i : D.nd.Loc) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))), GlobalTheory.SplitCoef.OSplitAt D i → GoodR D.nd i r → ∀ (K' : Type) [Field K'] (f : Kf D.nd i →+* K'), (∀ x W₁ W₂, IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ → IsIrrSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₂ → W₁ ⊓ W₂ = ⊥ → ¬ IsoSub (mapRep (f.comp (algebraMap (D.nd.O i) (Kf D.nd i))) (r x)) W₁ W₂) → ∀ x, AbsIrrDistinct (repK D.nd i r x) := by
  intro D i r hO hr K' _ f hd x
  exact _root_.GlobalTheory.absIrrDistinct_of_ss_of_absIrr_of_mapRep_distinct f (mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x)) (hr x).2.1 (hO x (r x) (hr x)) (hd x)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.CapLeWidth
section
open Formalism.MainNotions Formalism.BasicNotions Formalism.MainNotions.G Classical

namespace GlobalTheory.ShapeRows

theorem ent_nu {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.nu u j z = nuD D u j z := by
  apply YoungDiagram.ext
  ext ⟨r, c⟩
  rw [YoungDiagram.mem_cells, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen,
    YoungDiagram.mem_iff_lt_rowLen]
  have h : (E.nu u j z).rowLen r = (nuD D u j z).rowLen r := by
    have h1 := E.nu_row u j hj z r
    have h2 := nuRowOK D u j hj z r
    exact_mod_cast h1.trans h2.symm
  rw [h]

theorem ent_size {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.size u j z = (((nuD D u j z).card : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.size
  rw [ent_nu E u j hj z]

theorem ent_row {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) (r : ℕ) :
    E.row u j z r = (((nuD D u j z).rowLen r : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.row
  rw [ent_nu E u j hj z]

theorem ent_cap {D : D7} (E : OrbitPlaces.Ent D) (u : D.what₂.Word) (j : ℕ) (hj : j < D.R.m) (z : Bool × HH D) :
    E.cap u j z = if IsTopPl D z then (((nuD D u j z).rowLen 1 : ℕ) : ℝ) else (((nuD D u j z).rowLen 0 : ℕ) : ℝ) := by
  unfold OrbitPlaces.Ent.cap
  rw [ent_row E u j hj z, ent_row E u j hj z]

theorem cap_le_width : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ i : Fm.Ix x, ∀ (u : (Fm.D x i).what₂.Word), ∀ j < (Fm.D x i).R.m, ∀ (z : Bool × HH (Fm.D x i)), (if IsTopPl (Fm.D x i) z then (((nuD (Fm.D x i) u j z).rowLen 1 : ℕ) : ℝ) else (((nuD (Fm.D x i) u j z).rowLen 0 : ℕ) : ℝ)) ≤ (Fm.L x i).sc.b + (Fm.L x i).etaSz + 1 + 3 * (Fm.L x i).Sc := by
  intro eps Fm
  obtain ⟨x1, h1⟩ := GlobalTheory.Ggeo.wPl_windows Fm
  obtain ⟨x2, h2⟩ := GlobalTheory.LongRows.longRows Fm
  refine ⟨max x1 x2, fun x hx hx1 i u j hj z => ?_⟩
  obtain ⟨-, hw, -⟩ := h1 x (le_trans (le_max_left _ _) hx) hx1 i j hj z
  have hr := h2 x (le_trans (le_max_right _ _) hx) hx1 i u j hj z
  have hk : 5 ≤ (Fm.D x i).R.k := by
    have := (Fm.D x i).R.m_add_three_le_k
    have := (Fm.D x i).R.two_le_m
    omega
  have hN : (Fm.D x i).R.k ≤ (Fm.D x i).R.N j := by unfold Ranks.N; omega
  have hS := (Fm.L x i).Sc_pos
  split_ifs with hz
  · have e := nuRowOK (Fm.D x i) u j hj z 1
    rw [if_pos (by omega)] at e
    have := ((hr 1 (by omega)).2 hz le_rfl (by omega)).2
    rw [e]
    linarith
  · have e := nuRowOK (Fm.D x i) u j hj z 0
    rw [if_pos (by omega)] at e
    have := ((hr 0 (by omega)).1 hz).2
    rw [if_pos rfl] at this
    rw [e]
    linarith

theorem shape : ∀ {eps : ℝ} (Fm : FamP eps), ∃ x0 : ℝ, ∀ x ≥ x0, Fm.x1 < x → ∀ (i : Fm.Ix x) (Ee : OrbitPlaces.Ent (Fm.D x i)), OrbitPlaces.Shape (Fm.D x i) (Fm.L x i) (Fm.Gx x i) Ee := by
  intro eps Fm
  obtain ⟨a1, h1⟩ := GlobalTheory.Ggeo.wPl_pos Fm
  obtain ⟨a2, h2⟩ := GlobalTheory.ExcessLow.excess_mem_Icc Fm
  obtain ⟨a3, h3⟩ := GlobalTheory.TopExcess.top_excess Fm
  obtain ⟨a4, h4⟩ := GlobalTheory.TopFirstRow.two_w_le_first_row Fm
  obtain ⟨a5, h5⟩ := GlobalTheory.nuD_card_le_a_sq Fm
  obtain ⟨a6, h6⟩ := GlobalTheory.rank_two_logb_five_sq_le Fm
  obtain ⟨a7, h7⟩ := GlobalTheory.ShXa.X''_le_a Fm
  obtain ⟨a8, h8⟩ := GlobalTheory.family_one_lt_scale_a Fm
  obtain ⟨a9, h9⟩ := cap_le_width Fm
  obtain ⟨a10, h10⟩ := GlobalTheory.AlTop.al_le Fm
  obtain ⟨a11, h11⟩ := GlobalTheory.CapBound.cap_le Fm
  refine ⟨max a1 (max a2 (max a3 (max a4 (max a5 (max a6 (max a7 (max a8 (max a9 (max a10 a11))))))))),
    fun x hx hx1 i Ee => ?_⟩
  simp only [ge_iff_le, max_le_iff] at hx
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := hx
  exact
    { wpos := h1 x b1 hx1 i
      low := fun u j hj z hz => by
        rw [ent_size Ee u j hj z]
        exact h2 x b2 hx1 i u j hj z hz
      top := fun u j hj z hz => by
        rw [ent_size Ee u j hj z, ent_row Ee u j hj z]
        exact h3 x b3 hx1 i u j hj z hz
      top1 := fun u j hj z hz => by
        rw [ent_row Ee u j hj z]
        exact h4 x b4 hx1 i u j hj z hz
      sizeA := fun u j hj z => by
        rw [ent_size Ee u j hj z]
        exact h5 x b5 hx1 i u j hj z
      rankA := h6 x b6 hx1 i
      xa := ⟨h7 x b7 hx1 i, h8 x b8 hx1 i⟩
      capW := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h9 x b9 hx1 i u j hj z
      alG := fun u j hj t ht => by
        rw [ent_row Ee u j hj, ent_row Ee u j hj]
        exact h10 x b10 hx1 i u j hj t ht
      capG := fun u j hj z => by
        rw [ent_cap Ee u j hj z]
        exact h11 x b11 hx1 i u j hj z }

end GlobalTheory.ShapeRows
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChainCompatibleTwistTransport
section
noncomputable section

namespace GlobalTheory.ColPeriodCompare

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV _root_.Formalism.L2.Col Formalism.L2.Ker GlobalTheory.IndefiniteRowSideFullHecke

section Mem

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (L : Type) [Field L]

def unramOff (S : Set ℕ) (v : HeightOneSpectrum (𝓞 F)) : Subgroup (Chr F E L) :=
  ⨅ _ : ¬ GoodPl E S v, kills Lˣ (inertAt E v)

def IsTwist (S : Set ℕ) (x : Chr F E L) : Prop :=
  x ∈ finChar F E L ⊓ kills Lˣ (idF F E).range ⊓ (⨅ v : HeightOneSpectrum (𝓞 F), kills Lˣ (wildAt E v)) ∧
    x ∈ ⨅ v : HeightOneSpectrum (𝓞 F), unramOff F E L S v

end Mem

section Transport

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S S' : Set ℕ}
  {χ : Chr X.F X.E X.K} (h : IsTwist X.F X.E X.K S χ) (h' : IsTwist X.F X.E X.K S' χ)
  (cst : LocCst X (uSG Pr.vGs (QE sel χ))) (L : ChIdx X Pr R (QE sel χ))

end Transport

section Chain

variable (D : D7) (EX : ErrX D) (Ch : Chars (ColumnAvoidanceConditions.fieldsOf D) (ColumnAvoidanceConditions.primesOf D EX) D.R.m)
  (m0 : Fin D.R.m → Formalism.L2.Host.HChar D.host.E)
  (sel : HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).F) → HeightOneSpectrum (𝓞 (ColumnAvoidanceConditions.fieldsOf D).E)) {S S' : Set ℕ}
  (A : Amb (ColumnAvoidanceConditions.fieldsOf D)) (u : D.what₂.Word) (μ : D.what₂.Tup)

end Chain

end GlobalTheory.ColPeriodCompare
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnFieldRamificationIdxInEqOne
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col NumberField IsDedekindDomain

namespace GlobalTheory.ColumnField

theorem conj_notMem_inertia (D : D7) (X : Fields) (s : Seam D X) (hs : s.Ok) (P : HeightOneSpectrum (𝓞 X.E)) :
    ¬ ∀ x : 𝓞 X.E, X.conjO x - x ∈ P.asIdeal := by
  intro hall
  let φ : 𝓞 X.E ≃+* 𝓞 D.host.E := RingOfIntegers.mapRingEquiv s.iE
  let P' : Ideal (𝓞 D.host.E) := P.asIdeal.comap (φ.symm : 𝓞 D.host.E →+* 𝓞 X.E)
  have hmax : P'.IsMaximal :=
    have := P.isMaximal
    Ideal.comap_isMaximal_of_surjective _ φ.symm.surjective
  obtain ⟨θ, t, h1, h2⟩ := Formalism.BasicNotions.Examples₂.unram_at D.host P' hmax
  have hcoe : ∀ y : 𝓞 X.E, algebraMap (𝓞 D.host.E) D.host.E (φ y) = s.iE (algebraMap (𝓞 X.E) X.E y) := fun _ => rfl
  have e : φ.symm t = X.conjO (φ.symm θ) := by
    apply φ.injective
    apply RingOfIntegers.ext
    rw [RingEquiv.apply_symm_apply]
    change algebraMap (𝓞 D.host.E) D.host.E t = algebraMap (𝓞 D.host.E) D.host.E (φ (X.conjO (φ.symm θ)))
    rw [hcoe, h1]
    change _ = s.iE (star (algebraMap (𝓞 X.E) X.E (φ.symm θ)))
    rw [hs.2, ← hcoe, RingEquiv.apply_symm_apply]
  apply h2
  change φ.symm (θ - t) ∈ P.asIdeal
  rw [map_sub, e, ← neg_sub]
  exact P.asIdeal.neg_mem (hall _)

theorem ramificationIdxIn_eq_one : ∀ (D : D7) (X : Fields) (s : Seam D X), X.Ok → s.Ok →
    ∀ v : HeightOneSpectrum (𝓞 X.F), v.asIdeal.ramificationIdxIn (𝓞 X.E) = 1 := by
  intro D X s hX hs v
  have : Algebra.IsQuadraticExtension X.F X.E := ⟨hX.rankE⟩
  have : IsGalois X.F X.E := inferInstance
  have := v.isMaximal
  obtain ⟨Q, hQ, hlo⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 X.E) v.asIdeal
  have hQ0 : Q ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q
  let P : HeightOneSpectrum (𝓞 X.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hun := hX.unram_of_inertia (conj_notMem_inertia D X s hs) P
  have hcomap : Q.comap (algebraMap (𝓞 X.F) (𝓞 X.E)) = v.asIdeal := (Ideal.over_def Q v.asIdeal).symm
  have hun' : ¬ v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 2 := by
    rw [← hcomap]
    exact hun
  have h1 : v.asIdeal.map (algebraMap (𝓞 X.F) (𝓞 X.E)) ≤ Q ^ 1 := by
    rw [pow_one, Ideal.map_le_iff_le_comap, hcomap]
  have he : v.asIdeal.ramificationIdx' Q = 1 := Ideal.ramificationIdx_spec h1 hun'
  have := hQ.isPrime
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx _ Q (X.E ≃ₐ[X.F] X.E),
    ← Ideal.ramificationIdx'_eq_ramificationIdx _ _ v.ne_bot]
  exact he

end GlobalTheory.ColumnField
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ColumnWeightComparison
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

namespace GlobalTheory.Proof.ColumnWeightComparison

theorem colGeTw_of_cmpLite {D : D7} (c : LatCmp D) (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup)
    (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    {Fl : Fills (D.gat u w hg)} {Lv : Levels Fl} (Ch : Chain Lv) (h : CmpLite D c Tw u μ w hg Ch)
    (x : ((D.fm u).lat 0).V) (s : ℝ)
    (hx : vGeLat (D.gat u w hg) (Lv.Int D.R.m) (Ch.chainK D.R.m (c.cmp u w hg x)) s) :
    WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s := by
  obtain ⟨cmp, h0, hK, hrat, hval⟩ := h
  obtain ⟨y, hy, hy'⟩ := GlobalTheory.Proof.LatticeValuationBound.exists_chain (Tw.fm u μ) Ch (c.embW u w hg) cmp hK hrat
    (Tw.e0 u μ x) D.R.m le_rfl
  refine ⟨y, ?_, hval y s (by rw [hy', h0]; exact hx)⟩
  rw [hy, Tw.embed_mul_block_embedding]
  rfl

theorem colGe0_of_colGeTw {D : D7} (Tw : TwForms D) (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (x : ((D.fm u).lat 0).V) (s : ℝ) (h0 : Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : WeilJacquetShalikaLaw.ColGeTw Tw u D.what₂.mu0 w x s) : WeilJacquetShalikaLaw.ColGe0 D u w x s := by
  obtain ⟨y, hy, hv⟩ := h
  refine ⟨(Tw.eMu0 u D.R.m le_rfl).symm y, ?_,
    GlobalTheory.Proof.LatticeValuationBound.VGe_symm _ _ _ (Tw.eMu0_lat u D.R.m le_rfl) hv⟩
  have h1 := Tw.eMu0_emb u D.R.m le_rfl ((Tw.eMu0 u D.R.m le_rfl).symm y)
  rw [LinearEquiv.apply_symm_apply, hy] at h1
  have h2 := Tw.eMu0_emb u 0 (Nat.zero_le _) x
  rw [← h0, Tw.embed_mul_block_embedding] at h2
  exact eq_of_heq (h1.symm.trans (GlobalTheory.Proof.LatticeValuationBound.col_heq (D.memberColumns_twistedChain_base u) h2))

theorem cmpV_of_cmpLite (D : D7) (Y : LatInst D) (c : LatCmp D) (Dx : DivX D) (Tw : TwForms D)
    (LC : D.what₂.Tup → ∀ u (w : D.what₂.places.Pl) (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
      Σ Lv : Levels (Y.Fl u w hg), Chain Lv)
    (h0 : ∀ u, Tw.e0 u D.what₂.mu0 = Tw.eMu0 u 0 (Nat.zero_le _))
    (h : ∀ μ, DV.Used D μ → ∀ u (w : D.what₂.places.Pl)
      (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)), D.what₂.places.resChar w ∉ Dx.Qp μ →
      CmpLite D c Tw u μ w hg (LC μ u w hg).2) :
    WeilJacquetShalikaLaw.CmpV c Dx Tw (reW Y LC) := by
  intro u w hg μ hU hQ x s hx
  have key : WeilJacquetShalikaLaw.ColGeTw Tw u μ w x s :=
    colGeTw_of_cmpLite c Tw u μ w hg (LC μ u w hg).2 (h μ hU u w hg hQ) x s hx
  refine ⟨?_, fun _ => key⟩
  rintro rfl
  exact colGe0_of_colGeTw Tw u w x s (h0 u) key

end GlobalTheory.Proof.ColumnWeightComparison
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConstantCoeffJetLogG
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.BeProps

open MvPowerSeries GlobalTheory.ThStr Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric

variable {l : ℕ} [hl : Fact l.Prime] {d : ℕ}

theorem norm_eq_one_of_pow {n : ℕ} (hn : 0 < n) {a : ℂ_[l]} (ha : a ^ n = 1) : ‖a‖ = 1 := by
  have h : ‖a‖ ^ n = 1 := by rw [← norm_pow, ha, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hn.ne').1 h

theorem norm_le_one_of_mem_Wp {w : ℂ_[l]} (hw : w ∈ Wp l) : ‖w‖ ≤ 1 := by
  have hc : IsClosed {x : ℂ_[l] | ‖x‖ ≤ 1} := isClosed_le continuous_norm continuous_const
  refine closure_minimal (t := {x : ℂ_[l] | ‖x‖ ≤ 1}) (fun x hx => ?_) hc hw
  change ‖x‖ ≤ 1
  induction hx using Subring.closure_induction with
  | mem x hx => obtain ⟨n, hn, -, h⟩ := hx; exact (norm_eq_one_of_pow hn h).le
  | zero => simp
  | one => simp
  | add x y _ _ hx hy => exact (IsUltrametricDist.norm_add_le_max x y).trans (max_le hx hy)
  | neg x _ hx => simpa using hx
  | mul x y _ _ hx hy => rw [norm_mul]; exact mul_le_one₀ hx (norm_nonneg _) hy

variable [NeZero d]

theorem constantCoeff_laS (s : ZMod d) : constantCoeff (laS l d s) = 0 :=
  (GlobalTheory.BiextInhab.laK_idMod2 (K := ℂ_[l]) (d := d) hl.out).1 s

theorem constantCoeff_laAt {κ : Type} [Finite κ] (ι : ZMod d → κ) (s : ZMod d) :
    constantCoeff (laAt (l := l) ι s) = 0 :=
  constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _)
    (fun _ => constantCoeff_X _) (constantCoeff_laS s)

theorem coeff_subst_range {K σ : Type*} [CommRing K] {G : MvPowerSeries σ K}
    (hG : MvPowerSeries.constantCoeff G = 0) (f : PowerSeries K) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (f.subst G) =
      ∑ n ∈ Finset.range ((α.sum fun _ k => k) + 1),
        PowerSeries.coeff n f * MvPowerSeries.coeff α (G ^ n) := by
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.of_constantCoeff_zero hG),
    finsum_eq_sum_of_support_subset (s := Finset.range ((α.sum fun _ k => k) + 1))]
  · rfl
  · intro k hk
    by_contra h
    apply hk
    have hlt : (α.sum fun _ k => k) < k := by simpa using h
    have h0 : MvPowerSeries.coeff α (G ^ k) = 0 := by
      apply MvPowerSeries.coeff_of_lt_order
      refine lt_of_lt_of_le ?_ (MvPowerSeries.le_order_pow_of_constantCoeff_eq_zero k hG)
      exact_mod_cast hlt
    simp [h0]

theorem expMv_eq_subst {σ : Type*} {G : MvPowerSeries σ ℂ_[l]} (hG : MvPowerSeries.constantCoeff G = 0) :
    expMv G = (PowerSeries.exp ℂ_[l]).subst G := by
  ext α
  rw [coeff_subst_range hG]
  show expMv G α = _
  rw [expMv]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [div_eq_inv_mul]

theorem subst_psubst {σ τ : Type} [Finite σ] {b : σ → MvPowerSeries τ ℂ_[l]} (hb : HasSubst b)
    {f : MvPowerSeries σ ℂ_[l]} (hf : constantCoeff f = 0) (g : PowerSeries ℂ_[l]) :
    subst b (PowerSeries.subst f g) = PowerSeries.subst (subst b f) g := by
  have ha : HasSubst (fun _ : Unit => f) := hasSubst_of_constantCoeff_zero fun _ => hf
  unfold PowerSeries.subst
  rw [subst_comp_subst_apply ha hb]

end GlobalTheory.BeProps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIsFrobWToC
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.FrobeniusOrbits GlobalTheory.TwU Classical

noncomputable section

namespace GlobalTheory.TwU

theorem wHom_ext (p : ℕ) [Fact p.Prime] (f g : Formalism.L2.G.Pend.WW p →+* ℂ_[p])
    (hf : ∀ x, ‖f x‖ ≤ 1) (hg : ∀ x, ‖g x‖ ≤ 1)
    (ht : ∀ y, f (WittVector.teichmuller p y) = g (WittVector.teichmuller p y)) (x : Formalism.L2.G.Pend.WW p) :
    f x = g x := by
  refine Formalism.L2.G.Pend.eq_of_close p fun N => ?_
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff x N
  set S := ∑ i ∈ Finset.Iic N, (WittVector.teichmuller p
        (((_root_.frobeniusEquiv (Formalism.L2.G.Pend.kb p) p).symm ^ i) (x.coeff i)) * (p : Formalism.L2.G.Pend.WW p) ^ i) with hS
  have hfS : f S = g S := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hS, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast, ht]
  have hx : x = S + (p : Formalism.L2.G.Pend.WW p) ^ (N + 1) * c := by rw [← hc]; ring
  have hpC : ‖(p : ℂ_[p])‖ = (p : ℝ)⁻¹ := Formalism.L2.G.Pend.norm_p_C p
  have e : f x - g x = (p : ℂ_[p]) ^ (N + 1) * (f c - g c) := by
    rw [hx, map_add (f := _), map_add (f := _), hfS, map_mul, map_mul, map_pow, map_pow, map_natCast, map_natCast]; ring
  rw [e, norm_mul, norm_pow, hpC]
  have h1 : ‖f c - g c‖ ≤ 1 := Formalism.L2.G.Pend.nsub p (hf c) (hg c)
  calc ((p : ℝ)⁻¹) ^ (N + 1) * ‖f c - g c‖ ≤ ((p : ℝ)⁻¹) ^ (N + 1) * 1 :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N * (p : ℝ)⁻¹ := by rw [mul_one, pow_succ]
    _ ≤ ((p : ℝ)⁻¹) ^ N * 1 := mul_le_mul_of_nonneg_left (Formalism.L2.G.Pend.r_lt_one p).le (by positivity)
    _ = ((p : ℝ)⁻¹) ^ N := mul_one _

theorem wToC_frob (p : ℕ) [Fact p.Prime] (σ : ℂ_[p] →+* ℂ_[p]) (hσ : ∀ x, ‖σ x‖ = ‖x‖)
    (hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → σ ζ = ζ ^ p) (x : FormalGroupSystem.WW p) :
    σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  have := wHom_ext p (σ.comp (Formalism.L2.G.Pend.wToC p)) ((Formalism.L2.G.Pend.wToC p).comp (sigW p))
    (fun y => by rw [RingHom.comp_apply, hσ]; exact Formalism.L2.G.Pend.norm_wToC_le p y)
    (fun y => Formalism.L2.G.Pend.norm_wToC_le p _) (fun y => ?_) x
  · exact this
  · rw [RingHom.comp_apply, RingHom.comp_apply]
    have hs : sigW p (WittVector.teichmuller p y) = WittVector.teichmuller p (y ^ p) := by
      show WittVector.frobenius (WittVector.teichmuller p y) = _
      rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]
    rw [hs, map_pow (WittVector.teichmuller p), map_pow (Formalism.L2.G.Pend.wToC p)]
    by_cases hy : y = 0
    · subst hy
      rw [WittVector.teichmuller_zero, map_zero, map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
    · obtain ⟨m, hm, hc, h1⟩ := Formalism.L2.G.Pend.exists_coprime_pow_eq_one p hy
      exact hζ _ m hm hc (by rw [← map_pow, ← map_pow, h1, map_one, map_one])

theorem exists_isFrob_wToC : ∀ (p : ℕ) [Fact p.Prime], ∃ σ : ℂ_[p] →+* ℂ_[p], GlobalTheory.ThBe0.IsFrob σ ∧
    ∀ x : FormalGroupSystem.WW p, σ (Formalism.L2.G.Pend.wToC p x) = Formalism.L2.G.Pend.wToC p (sigW p x) := by
  intro p _
  obtain ⟨g, hg⟩ := GlobalTheory.ThBe0.exists_gal_pow p
  have hζ : ∀ (ζ : ℂ_[p]) (n : ℕ), 0 < n → Nat.Coprime n p → ζ ^ n = 1 → Formalism.Per.σC g ζ = ζ ^ p := by
    intro ζ n hn hnl h
    obtain ⟨a, rfl, ha⟩ := GlobalTheory.ThBe0.exists_coe_eq_of_pow_eq_one p ζ n hn h
    rw [GlobalTheory.RingBasics.σC_coe, hg a n hnl ha]
    exact map_pow (algebraMap (PadicAlgCl p) ℂ_[p]) a p
  exact ⟨Formalism.Per.σC g, GlobalTheory.ThBe0.isFrob_of_rootOfUnity _ (GlobalTheory.RingBasics.norm_σC g) hζ,
    wToC_frob p _ (GlobalTheory.RingBasics.norm_σC g) hζ⟩

end GlobalTheory.TwU
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.JumpsOfCrystallineTwistBlockDecompositionStatement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jumps_of_crystalline_twist_block_decomposition : ∀ {D : D7} (L : SizeData₂ D) (C₀ : ℝ) (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i) (ε : ℤˣ) (κ : D.host.E →+* ↥C.LL.1), Roomy L C₀ → Formalism.MainNotions.LocalSituation.adm7 D → (∀ (A A' : GRep (Br.G D.nbr i w hw) ℚ_[D.nd.l i] ↥C.LL.1 ↥(OL C.LL)) (Pr : A.V →ₗ[↥C.LL.1] A'.V →ₗ[↥C.LL.1] ↥C.LL.1), IsDual1 (Br.PD D.loc D.nbr i w hw) A.ρ A'.ρ Pr → IsCrys (Br.PD D.loc D.nbr i w hw) A.ρ → IsCrys (Br.PD D.loc D.nbr i w hw) A'.ρ) → (∀ z : ℚ_[D.nd.l i], C.inc (algebraMap _ _ z) = algebraMap _ _ z) → (∀ x, Continuous (C.loc (rTwO D.nd i r x))) → Continuous (C.loc (WpO D.nd i ρ π)) → (∀ x, IsCrys (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rTwO D.nd i r x)))) → GlobalTheory.IndefiniteRowSideFullHecke.CrystallineAtPlaces.Splits D i r ρ π → (∀ τ : Br.Kw D.nbr i w hw →ₐ[ℚ_[D.nd.l i]] ↥C.LL.1, ∃ g, Reads (K := (D.nbr i w hw).Kw) D.host (Br.cEw D.nbr i w hw) κ τ g ∧ (∀ x a, IsJumpV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (rDuO D.nd i r x))) τ a → a ∈ jT1 (hcAt D g) (liftIdx D i) (pos ε g)) ∧ ∀ a : ℤ, multV (Br.PD D.loc D.nbr i w hw) (matRep (C.loc (T2O D.nd i ρ π))) τ a = if a ∈ jT2 (hcAt D g) (liftIdx D i) (pos ε g) then 1 else 0) → JumpIn (D.loc (D.nd.l i)) (K := (D.nbr i w hw).Kw) D (liftIdx D i) ε (Br.cEw D.nbr i w hw) κ (fun x => C.loc (rDuO D.nd i r x)) (C.loc (T2O D.nd i ρ π)) := by
  first | exact @GlobalTheory.HTW.Rec.jumpIn_of_reads | exact GlobalTheory.HTW.Rec.jumpIn_of_reads | (intros; apply GlobalTheory.HTW.Rec.jumpIn_of_reads <;> assumption)
end

