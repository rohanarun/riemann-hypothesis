module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1150
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1143
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2672
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2636
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1105
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0020
public import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2663
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1421
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.ExistsGenPullTriv
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0812
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2648
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0120
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2573
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2664
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2584
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
public import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2593
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2612
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2650
public import Development.AbelianVarietyTheory.Definitions.Divisors.LabRange

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothMetricCutTopChernDensityPatch
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option autoImplicit false

namespace GlobalTheory.GoodTop

theorem hasInt_cut_topDens_patch : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)} {S : Finset (Fin X.dim)} {A : Mat (fun _ : Unit => m) X.Fn} {W : Set (CxPts X.str σ)} {c : ℝ}, GoodPatch E O H e S A W c → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → tsupport ρ ⊆ W → HasInt (fun c : AlgChart X.str σ X.dim => c.e) (fun c y => ρ y * topDens E H₀ c y) (ptsIn X.str σ ⊤) ((Real.pi ^ X.dim)⁻¹ * (∫ v in e '' W, (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v).re) := by
  intro F _ σ X m E O H H₀ hH hH₀ e S A W c hp ρ hρ hsupp
  haveI := CxPts.secondCountableTopology_of_isProjOver σ X.isProjOver
  have hcont : Continuous ρ := continuous_iff_continuousAt.2 fun y => (hρ y).continuousAt
  have htop : ptsIn X.str σ ⊤ = Set.univ := Set.eq_univ_of_forall fun _ => mem_ptsIn_top
  set f : V X.dim → ℂ := fun v => (ρ (e.symm v) : ℂ) * mixTop fun _ => curvAt (fun v => H₀ A (e.symm v) ()) v with hf
  set g : V X.dim → ℝ := fun v => (Real.pi ^ X.dim)⁻¹ * (f v).re with hg
  obtain ⟨hUo, -, hK⟩ := _root_.GlobalTheory.GoodTop.goodPatch_image E O H hp

  have hfi : IntegrableOn f (e '' W) := by
    refine _root_.GlobalTheory.GoodTop.integrableOn_cut_mixTop_smooth (e '' W) (e '' tsupport ρ) (fun v => H₀ A (e.symm v) ()) (fun v => ρ (e.symm v)) hUo
      (hK _ (isClosed_tsupport ρ) hsupp) (Set.image_mono hsupp) ?_ ?_ ?_
    · rintro _ ⟨z, hz, rfl⟩
      exact _root_.GlobalTheory.GoodTop.gram_smooth_isUnit_holoChart E ⊤ H₀ hH₀ hp.holo mem_ptsIn_top (hp.sub hz) (hp.frame z hz)
    · rintro _ ⟨z, hz, rfl⟩
      exact (_root_.GlobalTheory.GoodTop.contDiffAt_holoChart hp.holo (hp.sub hz) (hρ z)).contDiffWithinAt
    · rintro _ ⟨z, hz, rfl⟩ hK'
      rw [e.left_inv (hp.sub hz)]
      by_contra h0
      exact hK' ⟨z, subset_tsupport ρ h0, rfl⟩
  have hgi : IntegrableOn g (e '' W) := hfi.re.const_mul _
  have key := _root_.GlobalTheory.GoodTop.hasInt_of_chart (fun c : AlgChart X.str σ X.dim => c.e)
    (fun i j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart i.holo j) (fun y => AlgChart.exists_mem_source y)
    (S := ptsIn X.str σ ⊤) (isOpen_ptsIn _).measurableSet (d := fun c y => ρ y * topDens E H₀ c y) e W g
    hp.isOpen hp.sub (fun j => GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart hp.holo j) (_root_.GlobalTheory.GoodTop.isTopForm_mul_topDens E ⊤ H₀ hH₀ hcont) ?_ ?_
    (by rw [htop, Set.univ_inter]; exact hgi)
  · rw [htop, Set.univ_inter] at key
    convert key using 1
    rw [hg, integral_const_mul]
    congr 1
    exact (integral_re hfi).symm
  · intro i y _ hyW _
    have : ρ y = 0 := by
      by_contra h0
      exact hyW (hsupp (subset_tsupport ρ h0))
    simp [this]
  · intro j y _ hyW hyj
    have ht := _root_.GlobalTheory.GoodTop.topDens_holoChart E ⊤ H₀ hH₀ hp.holo j mem_ptsIn_top (hp.sub hyW) hyj (hp.frame y hyW)
    simp only [hg, hf, e.left_inv (hp.sub hyW), Complex.re_ofReal_mul]
    rw [← mul_assoc, mul_comm _ (ρ y), mul_assoc, ht]
    ring

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleGaloisImagesCommuteOfComplexMultiplica
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj Pointwise
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.Published GlobalTheory.Published.AbVarRed IsLocalRing
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CMComm

theorem commute_of_cyclic {l : ℕ} [Fact l.Prime] {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    [Module.IsTorsionFree ℤ_[l] T] {O : Type} [CommRing O] (ρ : O →+* Module.End ℤ_[l] T) (v : T) (c : ℤ_[l])
    (hc : c ≠ 0) (hv : ∀ t : T, c • t ∈ Submodule.span ℤ_[l] (Set.range fun a => ρ a v))
    (g h : Module.End ℤ_[l] T) (hg : ∀ a, g * ρ a = ρ a * g) (hh : ∀ a, h * ρ a = ρ a * h) :
    g * h = h * g := by
  set P := Submodule.span ℤ_[l] (Set.range ρ) with hP
  have hcen : ∀ k : Module.End ℤ_[l] T, (∀ a, k * ρ a = ρ a * k) → ∀ x ∈ P, k * x = x * k := by
    intro k hk x hx
    have : P ≤ Subalgebra.toSubmodule (Subalgebra.centralizer ℤ_[l] {k}) := by
      rw [hP, Submodule.span_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff]
      rintro _ rfl
      exact hk a
    have h1 := this hx
    rw [Subalgebra.mem_toSubmodule, Subalgebra.mem_centralizer_iff] at h1
    exact h1 k rfl
  have hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := by
    intro x hx y hy
    have hx' : ∀ a, x * ρ a = ρ a * x := fun a => by
      have := hcen (ρ a) (fun b => by rw [← map_mul, ← map_mul, mul_comm]) x hx
      exact this.symm
    exact hcen x hx' y hy
  have hev : ∀ w : T, ∃ x ∈ P, x v = c • w := by
    intro w
    have := hv w
    rw [show (Set.range fun a => ρ a v) = (LinearMap.applyₗ v : Module.End ℤ_[l] T →ₗ[ℤ_[l]] T) '' Set.range ρ by
      rw [← Set.range_comp]; rfl, Submodule.span_image] at this
    obtain ⟨x, hx, e⟩ := this
    exact ⟨x, hx, e⟩
  refine LinearMap.ext fun t => ?_
  obtain ⟨x, hx, ex⟩ := hev t
  obtain ⟨y, hy, ey⟩ := hev (g v)
  obtain ⟨z, hz, ez⟩ := hev (h v)
  have hgx := hcen g hg x hx
  have hhx := hcen h hh x hx
  have k1 : c • c • c • (g * h) t = x (z (y v)) := by
    have e1 : c • (g * h) t = x (g (h v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (g * (h * x)) v = x (g (h v))
      rw [hhx, ← _root_.mul_assoc, hgx, _root_.mul_assoc]; rfl
    have e2 : c • x (g (h v)) = x (z (g v)) := by
      rw [← map_smul, ← map_smul, ← ez]
      change x ((g * z) v) = x ((z * g) v)
      rw [hcen g hg z hz]
    rw [e1, e2, ← map_smul, ← map_smul, ← ey]
  have k2 : c • c • c • (h * g) t = x (y (z v)) := by
    have e1 : c • (h * g) t = x (h (g v)) := by
      rw [← map_smul, ← ex, Module.End.mul_apply]
      change (h * (g * x)) v = x (h (g v))
      rw [hgx, ← _root_.mul_assoc, hhx, _root_.mul_assoc]; rfl
    have e2 : c • x (h (g v)) = x (y (h v)) := by
      rw [← map_smul, ← map_smul, ← ey]
      change x ((h * y) v) = x ((y * h) v)
      rw [hcen h hh y hy]
    rw [e1, e2, ← map_smul, ← map_smul, ← ez]
  have k3 : x (z (y v)) = x (y (z v)) := by
    change (x * (z * y)) v = (x * (y * z)) v
    rw [hcomm z hz y hy]
  have k4 : (c * c * c) • (g * h) t = (c * c * c) • (h * g) t := by
    rw [mul_smul, mul_smul, k1, k3, ← k2, mul_smul, mul_smul]
  exact smul_right_injective T (mul_ne_zero (mul_ne_zero hc hc) hc) k4

theorem galTate_comm_actTate {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] (A : Over (Sp K)) [GrpObj A]
    [IsCommMonObj A] {O : Type} [CommRing O] (α : OAct O A) (l : ℕ) [Fact l.Prime] (σ : Ω ≃ₐ[K] Ω) (a : O) :
    galTate A l σ * actTate α.toRingAct l (ptOver K Ω) a = actTate α.toRingAct l (ptOver K Ω) a * galTate A l σ :=
  LinearMap.ext fun t => Tate.ext fun n => by
    change specAut σ ≫ (t.lev n ≫ α.act a) = (specAut σ ≫ t.lev n) ≫ α.act a
    rw [Category.assoc]

theorem galTate_commute_of_hasCMBy : ∀ (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] [IsSepClosure K Ω] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (F : Type) [Field F] [NumberField F], HasCMBy A F → ∀ (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ σ τ : Ω ≃ₐ[K] Ω, galTate A l σ * galTate A l τ = galTate A l τ * galTate A l σ := by
  intro K Ω _ _ _ _ A _ _ hA F _ _ hF l _ hl σ τ
  obtain ⟨⟨d, hd, hdeg⟩, O, _, _, _, ⟨α⟩⟩ := hF
  haveI : IsSepClosed Ω := IsSepClosure.sep_closed K
  have hcard : ∀ n : ℕ, Nat.card {x : ptOver K Ω ⟶ A // x ^ (l ^ n) = 1} = l ^ (2 * d * n) := fun n => by
    rw [GlobalTheory.SepClosedTorsion.card_torsion_sepClosed K Ω A hA d hd (l ^ n) (by rw [Nat.cast_pow]; exact pow_ne_zero _ hl), ← pow_mul, mul_comm n]
  obtain ⟨hfree, hfin, hrank⟩ := GlobalTheory.TateFree.free_finite_finrank (ptOver K Ω ⟶ A) l (2 * d) hcard
  haveI := hfree
  haveI := hfin
  obtain ⟨v, c, hc, hv⟩ := _root_.GlobalTheory.CyclicLattice.exists_smul_mem_span_orbit l (Tate l (ptOver K Ω ⟶ A)) O F (actTate α.toRingAct l (ptOver K Ω))
    (hrank.trans hdeg.symm) (_root_.GlobalTheory.CMFaithful.linearIndependent_actTate K Ω A hA
      ⟨d, by have := Module.finrank_pos (R := ℚ) (M := F); omega, hd⟩ F O α l hl)
  exact commute_of_cyclic _ v c hc hv _ _ (galTate_comm_actTate A α l σ) (galTate_comm_actTate A α l τ)

end GlobalTheory.CMComm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateSimilitudeGeometricPointsOfGenericDvr
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
open GlobalTheory.UPel.HT

namespace GlobalTheory.HTGeomExt

variable {p : ℕ} [Fact p.Prime] {D : Datum p}

theorem tateIsoO_transport {k k' : Type} [Field k] [Field k'] {Q Q' : Type} [Group Q] [Group Q']
    {act : D.O → Q → Q} {act' : D.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → k'ˣ → Prop}
    (I : TateIsoO D k Q act e) (r : Q →* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hbij : ∀ n, 0 < n → n.Coprime p → Set.BijOn r {y : Q | y ^ n = 1} {y : Q' | y ^ n = 1})
    (ζ' : ℕ → k'ˣ) (hprim : ∀ n, 0 < n → n.Coprime p → IsPrimitiveRoot (ζ' n) n)
    (hpow : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → ζ' (n * m) ^ m = ζ' n)
    (hisom : ∀ n, 0 < n → n.Coprime p → ∀ x y,
      e' n (r (I.ev n x)) (r (I.ev n y)) (ζ' n ^ (2 * D.EF x y))) :
    ∃ I' : TateIsoO D k' Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) := by
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ x, I.ev n x ^ n = 1 :=
    fun n h1 h2 x => (I.onto n h1 h2 _).2 ⟨x, rfl⟩
  refine ⟨
    { ζ := ζ'
      ζ_prim := hprim
      ζ_pow := hpow
      ev := fun n x => r (I.ev n x)
      add := fun n x y => by simp only [I.add, map_mul]
      lin := fun n c x => by simp only [I.lin, hact]
      ker := fun n h1 h2 x => ?_
      onto := fun n h1 h2 q => ?_
      tower := fun n m h1 h2 h3 x => by simp only [← map_pow, I.tower n m h1 h2 h3]
      isom := hisom }, fun n x => rfl⟩
  · rw [← I.ker n h1 h2 x]
    constructor
    · intro h
      refine (hbij n h1 h2).injOn (htor n h1 h2 x) (show (1 : Q) ^ n = 1 from one_pow n) ?_
      rw [h, map_one]
    · intro h
      show r (I.ev n x) = 1
      rw [h, map_one]
  · constructor
    · intro hq
      obtain ⟨y, hy, rfl⟩ := (hbij n h1 h2).surjOn hq
      obtain ⟨x, hx⟩ := (I.onto n h1 h2 y).1 hy
      exact ⟨x, by rw [hx]⟩
    · rintro ⟨x, rfl⟩
      show r (I.ev n x) ^ n = 1
      rw [← map_pow, htor n h1 h2 x, map_one]

end GlobalTheory.HTGeomExt

namespace GlobalTheory.HTGeomExt

theorem tateIsoO_geom_of_generic : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (gm : R →+* W) (G : Over (Sp W)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme G → ∀ (act : OActN D.O G) (P : LB (G2 G).left), P.IsLB → ∀ (y : D.La → (𝟙_ (Over (Sp W)) ⟶ G)), (∀ x x', y (x + x') = y x * y x') → (∀ (k : Type) [Field k] [IsAlgClosed k] (β : L →+* k), ∃ I : TateIsoO D k (Over.mk (spMap (β.comp (algebraMap W L))) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x) → ∀ (k : Type) [Field k] [IsAlgClosed k] (β : W →+* k), ∃ I : TateIsoO D k (Over.mk (spMap β) ⟶ G) (fun c g => g ≫ act.act c) (fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)), ∀ x, toUnit _ ≫ y x = I.ev N x := by
  intro p _ D R _ b N W L _ _ _ _ _ _ gm G _ _ hab act P hP y hy hgen k _ _ β
  obtain ⟨V, j, h, hj, hx⟩ := _root_.GlobalTheory.geomPoint_factors_valuationSubring_algClosure W L k (spMap β)
  have hunit : ∀ n : ℕ, n.Coprime p → IsUnit (n : V) := fun n hn => by
    simpa using (b.unit n hn).map (j.comp gm)
  obtain ⟨r, hr1, hr2, hr3, hr4⟩ := _root_.GlobalTheory.ValReduction.reduction_points V (AlgebraicClosure L) k h (Sp W) G hab (spMap j)
  have hs : spMap ((algebraMap V (AlgebraicClosure L)).comp j) =
      spMap (algebraMap V (AlgebraicClosure L)) ≫ spMap j := by
    dsimp only [spMap]
    rw [CommRingCat.ofHom_comp, Spec.map_comp]
  have hg := hgen (AlgebraicClosure L) (algebraMap L (AlgebraicClosure L))
  rw [← hj, hs] at hg
  obtain ⟨I, hI⟩ := hg
  rw [hx]
  have hz : ∀ n, ∃ z : Vˣ, 0 < n → n.Coprime p →
      (algebraMap V (AlgebraicClosure L) (z : V) = (I.ζ n : AlgebraicClosure L) ∧
        IsPrimitiveRoot (Units.map (h : V →* k) z) n) := by
    intro n
    by_cases hn : 0 < n ∧ n.Coprime p
    · obtain ⟨z, ⟨hz1, hz2⟩, -⟩ := valuationRing_rootOfUnity_lift_reduce V (AlgebraicClosure L) k h n
        (hunit n hn.2) (I.ζ n) (I.ζ_prim n hn.1 hn.2).pow_eq_one
      exact ⟨z, fun _ _ => ⟨hz1, hz2 (I.ζ_prim n hn.1 hn.2)⟩⟩
    · exact ⟨1, fun h1 h2 => absurd ⟨h1, h2⟩ hn⟩
  choose z hz using hz
  have hzU : ∀ n, 0 < n → n.Coprime p →
      Units.map (algebraMap V (AlgebraicClosure L) : V →* AlgebraicClosure L) (z n) = I.ζ n :=
    fun n h1 h2 => Units.ext (hz n h1 h2).1
  have hinj : Function.Injective (algebraMap V (AlgebraicClosure L)) :=
    IsFractionRing.injective V (AlgebraicClosure L)
  have hLb := LB.isLB_pull hP (lift (𝟙 G) (𝟙 G)).left
  have hpow : ∀ n m : ℕ, 0 < n → 0 < m → (n * m).Coprime p →
      Units.map (h : V →* k) (z (n * m)) ^ m = Units.map (h : V →* k) (z n) := by
    intro n m h1 h2 h3
    have hn : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) h3
    rw [← map_pow]
    congr 1
    apply Units.ext
    apply hinj
    rw [Units.val_pow_eq_pow_val, map_pow, (hz _ (Nat.mul_pos h1 h2) h3).1, (hz n h1 hn).1,
      ← Units.val_pow_eq_pow_val, I.ζ_pow n m h1 h2 h3]
  have hisom : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ x x', Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n (r (I.ev n x)) (r (I.ev n x'))
      (unitOn (Units.map (h : V →* k) (z n) ^ (2 * D.EF x x'))) := by
    intro n h1 h2 x x'
    have hi := I.isom n h1 h2 x x'
    rw [← hzU n h1 h2, ← map_zpow] at hi
    have ho := hr4 _ hLb n (hunit n h2) _ _ (z n ^ (2 * D.EF x x'))
      ((I.onto n h1 h2 _).2 ⟨x, rfl⟩) ((I.onto n h1 h2 _).2 ⟨x', rfl⟩) hi
    rw [map_zpow] at ho
    exact ho
  obtain ⟨I', hI'⟩ := tateIsoO_transport (act' := fun c g => g ≫ act.act c)
    (e' := fun n g g' z => Out.WeilIs G (P.pull (lift (𝟙 G) (𝟙 G)).left) n g g' (unitOn z)) I r (fun c q => hr2 (act.act c) q)
    (fun n _ h2 => hr3 n (hunit n h2)) (fun n => Units.map (h : V →* k) (z n))
    (fun n h1 h2 => (hz n h1 h2).2) hpow hisom
  refine ⟨I', fun x => ?_⟩
  rw [hI', ← hI x]
  refine (hr1 (toUnit _ ≫ y x) _ _ ?_ ?_).symm
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, Over.comp_left]
    exact Category.assoc _ _ _

end GlobalTheory.HTGeomExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TautologicalCoordsEqOfMatchingData
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
noncomputable section

namespace GlobalTheory.TInj

theorem gm_unitOn_inj {V : Type} [CommRing V] [IsDomain V] {F : Type} [Field F] [Algebra (FractionRing V) F]
    (z : (TF (R := V) F).left) {k₁ k₂ : Fˣ}
    (h : gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₁) = gm (𝟙 (TF (R := V) F).left) z ⊤ (unitOn k₂)) : k₁ = k₂ := by
  have e : unitOn k₁ = unitOn k₂ := unit_ext fun x _ => by
    have : x = z := Subsingleton.elim (α := PrimeSpectrum F) x z
    rw [this]; exact h
  revert e
  apply Units.map_injective
  intro x y h
  have := congrArg (Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom h
  simpa using this

theorem cancel_four {G : Type} [CommGroup G] {V₁ V₂ K₁ K₂ L₁ L₂ U τ : G} (h₁ : V₁ = K₁ * (L₁ * τ))
    (h₂ : V₂ = K₂ * (L₂ * τ)) (h₃ : V₂ = V₁ * U) (h₄ : L₂ = L₁ * U) : K₁ = K₂ := by
  rw [h₄, h₃, h₁] at h₂
  have e : K₁ * (L₁ * U * τ) = K₂ * (L₁ * U * τ) := by rw [← h₂]; ac_rfl
  exact mul_right_cancel e

theorem coords_eq_of_match : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (ω : W →+* V) (D₁ D₂ : DegPre V) (s₁ : I → V) (e₁ : D₁.X ≃+ (Fin T.r → ℤ)) (β₁ : D₁.P.A.left ⟶ T.B.left) (ββ₁ : (G2 D₁.P.A).left ⟶ (G2 T.B).left) (w₁ : LB.Iso (abelian₂ D₁.P.A D₁.P.L) ((abelian₂ T.B T.M.L).pull ββ₁)) (s₂ : I → V) (e₂ : D₂.X ≃+ (Fin T.r → ℤ)) (β₂ : D₂.P.A.left ⟶ T.B.left) (ββ₂ : (G2 D₂.P.A).left ⟶ (G2 T.B).left) (w₂ : LB.Iso (abelian₂ D₂.P.A D₂.P.L) ((abelian₂ T.B T.M.L).pull ββ₂)) (b : D₁.P.A ⟶ D₂.P.A) (φ : D₁.X ≃+ D₂.X) (F : Type) [Field F] [Algebra (FractionRing V) F], 1 ≤ n → (∃ ε₀ : Module.Basis I ℤ (balForms (id : ℤ → ℤ) (Fin T.r → ℤ)), ∀ i, ε i = ε₀ i) → D₁.TauBimult → D₂.TauBimult → From T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ → From T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ → (∀ i, s₁ i ≠ 0) → (∀ i, s₂ i ≠ 0) → Match D₁ D₂ b φ F → (∀ y, e₂ (φ y) = e₁ y) → b.left ≫ β₂ = β₁ → (∀ a : Fin T.r → ℤ, ∃ (p₁ : QkPt D₁ F n) (p₂ : QkPt D₂ F n), p₁.y = e₁.symm a ∧ TautPt T ω s₁ ε n D₁ e₁ β₁ ββ₁ w₁ F a p₁.g ∧ p₂.y = e₂.symm a ∧ TautPt T ω s₂ ε n D₂ e₂ β₂ ββ₂ w₂ F a p₂.g ∧ QImg b φ p₁ p₂) → s₁ = s₂ := by
  intro o W _ _ _ T I _ ε n V _ _ ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b φ F _ _ hn hε hD₁ hD₂ hF₁ hF₂ hs₁ hs₂ hM he hb H
  obtain ⟨ε₀, hε₀⟩ := hε
  obtain ⟨hbm, -, -, hu, -⟩ := hM
  let f : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have key : ∀ c a : Fin T.r → ℤ, ∏ i, f (s₁ i) ^ ε i c a = ∏ i, f (s₂ i) ^ ε i c a := by
    intro c a
    obtain ⟨p₁, p₂, hy₁, ht₁, hy₂, ht₂, p', hy', hA, hE⟩ := H a
    have hg : p'.g = p₂.g := _root_.GlobalTheory.TInj.qkPt_g_eq_of_equiv V D₂ hD₂ F n hn p' p₂ (by
      rw [hy', hy₁, hy₂]; apply e₂.injective; rw [he, e₁.apply_symm_apply, e₂.apply_symm_apply]) hE
    rw [hg] at hA
    have hχ : e₁ (φ.symm (e₂.symm c)) = e₂ (e₂.symm c) := by rw [← he, φ.apply_symm_apply]
    obtain ⟨u, hun⟩ := hu (e₂.symm c)
    obtain ⟨k₁, hk₁, hv₁⟩ := ht₁.2 (φ.symm (e₂.symm c))
    obtain ⟨k₂, hk₂, hv₂⟩ := ht₂.2 (e₂.symm c)
    let z : (TF (R := V) F).left := (⊥ : PrimeSpectrum F)
    obtain ⟨J, hJ, -⟩ := exists_good (JN D₁ D₂) (jn_isLB D₁ D₂) z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    obtain ⟨J₀, hJ₀, -⟩ := exists_good T.M.L T.M.isLB z (K := Empty) Empty.elim Empty.elim
      (fun a => a.elim) (fun k => k.elim)
    have a₁ := hv₁ z J₀ (rl J) hJ₀ ((isPart_inl D₁.P.L D₂.P.L).good hJ)
    have a₂ := hv₂ z J₀ (rr J) hJ₀ ((isPart_inr D₁.P.L D₂.P.L).good hJ)
    have a₃ := hA.2 (e₂.symm c) u hun z J hJ
    have a₄ := _root_.GlobalTheory.TInj.lamVal_cmp T ε n V ω D₁ D₂ s₁ e₁ β₁ ββ₁ w₁ s₂ e₂ β₂ ββ₂ w₂ b hD₁ hD₂ hF₁ hF₂ hbm hb
      (φ.symm (e₂.symm c)) (e₂.symm c) hχ u hun (TF (R := V) F) p₁.g.b z J J₀ hJ hJ₀
    rw [← hA.1] at a₄
    rw [hχ] at a₁
    have hk : k₁ = k₂ := by
      apply gm_unitOn_inj z
      exact cancel_four a₁ a₂ a₃ a₄
    have := congrArg Units.val hk
    rw [hk₁, hk₂, hχ, e₂.apply_symm_apply] at this
    exact this
  simp only [hε₀] at key
  have hx := GlobalTheory.T.eq_of_prod_zpow_symmetricFormBasis_eq F T.r I ε₀ (fun i => f (s₁ i)) (fun i => f (s₂ i))
    (fun i => (map_ne_zero_iff f hf).2 (hs₁ i)) (fun i => (map_ne_zero_iff f hf).2 (hs₂ i)) (fun a b => key a b)
  funext i
  exact hf (congrFun hx i)

end GlobalTheory.TInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlace
section
noncomputable section

namespace GlobalTheory.KeyBadPrime

open AlgebraicGeometry CategoryTheory _root_.CategoryTheory.Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem key_unit_bad : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c κ hκ hpq la p hp hpl hbad T io e ho x hxs G t' m1 m2 n w hw θ hθ k hk
  obtain ⟨l₂, hd, hA, hg₂⟩ := _root_.GlobalTheory.GoodMultipleLevel.exists_good_multiple E H l
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₂ hpq
  obtain ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, x₂, r, m, he', hv, hφ, ho₂, hxs₂, hx₂⟩ :=
    _root_.GlobalTheory.LevelLift.lift_to_finer_level E H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hxs
  obtain ⟨G', t'', mt, m2', n', w', θ', k', hw', hθ', hk', hpb⟩ := GlobalTheory.T.exists_integralFramedData_completeDVR_extension E H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  obtain ⟨a₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨m1', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m (PullbackSections.sabMapCast a₁ hx₂.symm)
  obtain ⟨u', hu'⟩ := GlobalTheory.KeyIntegralVal.key_unit hκ hpq hg₂ ho₂ hxs₂ m1' m2' hw' hθ' k' hk'
  have h1 : (κ T'.Fr k' : T'.Fr) = iT (κ T.Fr k : T.Fr) := hκ.2.1 T.Fr T'.Fr iT k k' hpb
  set a : T.Fr := (κ T.Fr k : T.Fr) with ha
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hu0 : ∀ (V : CDVR) (u : V.Vˣ), vV V.V (algebraMap V.V V.Fr u) = 0 := by
    intro V u
    have hne : ∀ u : V.Vˣ, algebraMap V.V V.Fr u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
    have nn : ∀ b : V.V, 0 ≤ vV V.V (algebraMap V.V V.Fr b) := fun b => by
      by_cases h : algebraMap V.V V.Fr b = 0
      · simp [h, vV]
      have := (WithZero.log_le_log (valV_ne_zero (V := V.V) h) one_ne_zero).2
        (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ b)
      rw [WithZero.log_one] at this
      rw [vV]; omega
    have h := vV_mul (V := V.V) (hne u) (hne u⁻¹)
    rw [← map_mul, Units.mul_inv, map_one, show vV V.V (1 : V.Fr) = 0 by simp [vV]] at h
    have := nn u
    have := nn (u⁻¹ : V.Vˣ)
    omega
  have hva : vV T.V a = 0 := by
    have h2 := hv a
    rw [← h1, hu', hu0] at h2
    have : (0 : ℤ) < e' := by exact_mod_cast he'
    nlinarith
  have hvi : vV T.V a⁻¹ = 0 := by
    have h := vV_mul (V := T.V) ha0 (inv_ne_zero ha0)
    rw [mul_inv_cancel₀ ha0, show vV T.V (1 : T.Fr) = 0 by simp [vV], hva] at h
    omega
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hva.ge
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hvi.ge
  have hbb : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', mul_inv_cancel₀ ha0, map_one])
  exact ⟨⟨b, b', hbb, by rw [mul_comm]; exact hbb⟩, hb.symm⟩

end GlobalTheory.KeyBadPrime
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupRescaleIntoLocalRingClassicalTrait
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.GLiftRechart

theorem main : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X : Setup F W i), 1 ≤ g → 3 ≤ n → Odd n → IsOpenImmersion i → IsE8 W → ThetaInt F W i → IsProjOver X.M.s → ∀ (ε : Matrix (Fin 8) (Fin 8) ℤ → (X.ρ.P.A ⟶ X.ρ.P.A)), IsDiagEnd F W X.ρ.P X.u ε → ∀ (p : ℕ) [Fact p.Prime] (z : X.M.Z) (c : CTrait X p z), ∃ (c₀ : X.Ω₁) (hc : c₀ ≠ 0) (R' : Subalgebra X.o₁ X.Ω₁) (fg : R'.FG) (frac : ∀ x : X.Ω₁, ∃ a ∈ R', ∃ b ∈ R', x = a / b) (hth : ∀ x, c₀ * X.S.th x ∈ R') (hev : ∀ x k, c₀ * X.S.ev x k ∈ R') (ρ' : (X.S.rechart c₀ hc R' fg frac hth hev).Real) (ε' : Matrix (Fin 8) (Fin 8) ℤ → (ρ'.P.A ⟶ ρ'.P.A)), Same X.ρ ε ρ' ε' (fun x => x) (RingHom.id _) ∧ ρ'.i₀ = X.ρ.i₀ ∧ R' ≤ X.M.O ((gPt p ≫ c.y) (closedPoint (PadicAlgCl p))) ∧ ∃ y₀ : R' →+* PadicAlgCl p, (∀ a : R', y₀ a = X.M.val (gPt p ≫ c.y) a) ∧ ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ R' a)‖ ≤ 1 := by
  intro g n F W Z i X hg hn ho himm he8 hth hproj ε hε p _ z c
  set w : X.M.Z := (gPt p ≫ c.y) (IsLocalRing.closedPoint (PadicAlgCl p)) with hw
  have hwr : X.π w ∈ Set.range i := by
    refine ⟨(spMap c.ι ≫ c.T.y) (IsLocalRing.closedPoint (PadicAlgCl p)), ?_⟩
    have h := congrArg (fun f => f (IsLocalRing.closedPoint (PadicAlgCl p))) c.comm
    rw [hw]
    exact h.symm
  obtain ⟨U, c₀, hc, fg, frac, hth', hev, ρ', ε', u', hUa, hwU, hUi, hSame, hi₀, hdiag, hcomp⟩ :=
    _root_.GlobalTheory.Poinc.exists_rechart_affine g n F W Z i X hg hn ho himm he8 hth hproj ε hε w hwr
  have hle : X.M.ringOn (U : Set X.M.Z) ≤ X.M.O w := RatModel.ringOn_le_O hwU
  refine ⟨c₀, hc, X.M.ringOn (U : Set X.M.Z), fg, frac, hth', hev, ρ', ε', hSame, hi₀, hle, ?_⟩
  refine ⟨(X.M.valHom (gPt p ≫ c.y) w (RatModel.range_eq_singleton _ _)).comp
    (Subalgebra.inclusion hle).toRingHom, fun a => rfl, fun a => ?_⟩
  have hmem : algebraMap X.o₁ X.Ω₁ a ∈ X.M.O z := Subalgebra.algebraMap_mem _ a
  have h1 := c.norm_val_le ((X.M.stalkEquiv z).symm ⟨_, hmem⟩)
  simp only [CTrait.val] at h1
  rw [← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply] at h1
  simpa using h1

end GlobalTheory.Poinc.GLiftRechart
end

