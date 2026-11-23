module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HoweMaximalTori.MaxSplit
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0002
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0005
public import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Bundle0003
public import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.Bundle0004
public import Development.WeilBound.CoreStatements.LocalThetaKernels.Locpair
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LocpairU
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.PfDict
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0021
public import Development.WeilBound.CoreStatements.LocallyConstantCoinvariants.Bundle0001
public import Development.WeilBound.ThetaLifts.CartanFactorisation.Bundle0006
public import Development.WeilBound.ThetaLifts.CartanFactorisation.KillInf
public import Development.WeilBound.ThetaLifts.Reductions.ArchimedeanMatchedMapsCompare
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0689
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0698
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MemProdSpanInf
section
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

namespace GlobalTheory.CompanionTheory.LimV.Slices

variable {A B : Type}

theorem span_eval_eq_top (W : Submodule ℂ (B → ℂ)) [FiniteDimensional ℂ W] :
    Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) = ⊤ := by
  set E := Submodule.span ℂ (Set.range fun y : B =>
      ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) with hE
  have hbot : E.dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_dualCoannihilator] at hw
    have : (w : B → ℂ) = 0 := by
      funext y
      exact hw _ (Submodule.subset_span ⟨y, rfl⟩)
    exact (Submodule.mem_bot ℂ).2 (Subtype.ext this)
  have h := Subspace.dualCoannihilator_dualAnnihilator_eq (W := E)
  rw [hbot] at h
  rw [← h]
  simp

theorem mem_prodSpan_inf_left (U S : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) (hS : ∀ y, (fun x => G (x, y)) ∈ S) :
    G ∈ prodSpan (U ⊓ S) V := by
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hG
  choose a ha b hb hg using fun i => (g i).2
  let W : Submodule ℂ (B → ℂ) := Submodule.span ℂ (Set.range b)
  haveI : FiniteDimensional ℂ W := FiniteDimensional.span_of_finite ℂ (Set.finite_range b)
  have hWV : W ≤ V := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  let bw : Fin n → W := fun i => ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩
  let T : A → W := fun x => ∑ i, (f i * a i x) • bw i
  have hG' : ∀ x y, G (x, y) = ∑ i, f i * a i x * b i y := by
    intro x y
    rw [← hsum]
    simp only [Finset.sum_apply, Pi.smul_apply, hg, smul_eq_mul, mul_assoc]
  have hT : ∀ x y, (T x : B → ℂ) y = G (x, y) := by
    intro x y
    rw [hG']
    simp [T, bw]
  have hφS : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ S := by
    intro φ
    have hφ : φ ∈ Submodule.span ℂ (Set.range fun y : B =>
        ((LinearMap.proj y : (B → ℂ) →ₗ[ℂ] ℂ) ∘ₗ W.subtype : Module.Dual ℂ W)) := by
      rw [span_eval_eq_top]; trivial
    induction hφ using Submodule.span_induction with
    | mem φ h =>
      obtain ⟨y, rfl⟩ := h
      simpa [hT] using hS y
    | zero => exact S.zero_mem
    | add φ ψ _ _ h₁ h₂ => exact S.add_mem h₁ h₂
    | smul r φ _ h => exact S.smul_mem r h
  have hφU : ∀ φ : Module.Dual ℂ W, (fun x => φ (T x)) ∈ U := by
    intro φ
    have : (fun x => φ (T x)) = ∑ i, (f i * φ (bw i)) • a i := by
      funext x
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [T, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    exact U.sum_mem fun i _ => U.smul_mem _ (ha i)
  let c := Module.finBasis ℂ W
  have hdec : G = ∑ j, fun p : A × B => c.coord j (T p.1) * (c j : B → ℂ) p.2 := by
    funext ⟨x, y⟩
    rw [← hT, Finset.sum_apply]
    have h := congrArg (fun w : W => (w : B → ℂ) y) (c.sum_repr (T x))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at h
    simpa [Module.Basis.coord_apply] using h.symm
  rw [hdec]
  exact Submodule.sum_mem _ fun j _ => Submodule.subset_span
    ⟨_, ⟨hφU (c.coord j), hφS (c.coord j)⟩, _, hWV (c j).2, rfl⟩

theorem swap_mem_prodSpan (U : Submodule ℂ (A → ℂ)) (V : Submodule ℂ (B → ℂ))
    (G : A × B → ℂ) (hG : G ∈ prodSpan U V) : (fun p : B × A => G p.swap) ∈ prodSpan V U := by
  induction hG using Submodule.span_induction with
  | mem F h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    exact Submodule.subset_span ⟨b, hb, a, ha, by funext p; simp [mul_comm]⟩
  | zero => exact Submodule.zero_mem _
  | add F F' _ _ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | smul r F _ h => exact Submodule.smul_mem _ r h

theorem mem_prodSpan_inf_of_slices : ∀ {A B : Type} (U₁ S₁ : Submodule ℂ (A → ℂ))
    (U₂ S₂ : Submodule ℂ (B → ℂ)) (G : A × B → ℂ), G ∈ prodSpan U₁ U₂ →
    (∀ y, (fun x => G (x, y)) ∈ S₁) → (∀ x, (fun y => G (x, y)) ∈ S₂) →
    G ∈ prodSpan (U₁ ⊓ S₁) (U₂ ⊓ S₂) := by
  intro A B U₁ S₁ U₂ S₂ G hG h₁ h₂
  have hL := mem_prodSpan_inf_left U₁ S₁ U₂ G hG h₁
  have hR := mem_prodSpan_inf_left U₂ S₂ (U₁ ⊓ S₁) (fun p : B × A => G p.swap)
    (swap_mem_prodSpan _ _ G hL) (fun x => h₂ x)
  simpa using swap_mem_prodSpan _ _ _ hR

end GlobalTheory.CompanionTheory.LimV.Slices

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairSpaceCarriesFlat
section
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

section PairCarry

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem FlatFn.fin_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) {u : GL (Fin N) (Af E)}
    (hu : u ∈ KO E N) : e (x * finGL E N u) = e x := by
  have h := he.rinv x 1 u hu
  simpa [cf] using h

theorem FlatFn.inf_inv {N : ℕ} {e : GA E N → ℂ} (he : FlatFn e) (x : GA E N) (k : Kinf E N) :
    e (x * infGL E N (Unitary.toUnits k)) = e x := by
  have h := he.rinv x k 1 (one_mem _)
  simpa [cf] using h

theorem mul_mem_pairSpace (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (F : H E a b → ℂ) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) : (fun x => e₁ x.1 * e₂ x.2 * F x) ∈ pairSpace U₁' U₂' := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hG
    obtain ⟨ψ₁, k₁, i₁⟩ := c₁ φ₁ h₁
    obtain ⟨ψ₂, k₂, i₂⟩ := c₂ φ₂ h₂
    refine Submodule.subset_span ⟨ψ₁, k₁, ψ₂, k₂, funext fun x => ?_⟩
    simp only [i₁, i₂]
    ring
  | zero =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (0 : H E a b → ℂ) x) = 0 := by
      funext x; simp
    rw [this]
    exact Submodule.zero_mem _
  | add G G' _ _ h h' =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (G + G') x) =
        (fun x => e₁ x.1 * e₂ x.2 * G x) + fun x => e₁ x.1 * e₂ x.2 * G' x := by
      funext x; simp only [Pi.add_apply]; ring
    rw [this]
    exact Submodule.add_mem _ h h'
  | smul c G _ h =>
    have : (fun x : H E a b => e₁ x.1 * e₂ x.2 * (c • G) x) = c • fun x => e₁ x.1 * e₂ x.2 * G x := by
      funext x; simp only [Pi.smul_apply, smul_eq_mul]; ring
    rw [this]
    exact Submodule.smul_mem _ c h

theorem pair_carry (e₁ : GA E a → ℂ) (e₂ : GA E b → ℂ) (U₁ U₁' : Submodule ℂ (Sm E a))
    (U₂ U₂' : Submodule ℂ (Sm E b)) (K₁ : Subgroup (GL (Fin a) (Af E))) (K₂ : Subgroup (GL (Fin b) (Af E)))
    (W₁ : Submodule ℂ (Kinf E a → ℂ)) (W₂ : Submodule ℂ (Kinf E b → ℂ)) (F : H E a b → ℂ)
    (f₁ : FlatFn e₁) (f₂ : FlatFn e₂) (c₁ : Carries e₁ U₁ U₁') (c₂ : Carries e₂ U₂ U₂')
    (hF : F ∈ pairSpace U₁ U₂) (hT : TypeH K₁ K₂ W₁ W₂ F) :
    (fun x => e₁ x.1 * e₂ x.2 * F x) ∈
      (pairSpace U₁' U₂' ⊓ typeHF (K₁ ⊓ KO E a) (K₂ ⊓ KO E b) W₁ W₂ : Submodule ℂ (H E a b → ℂ)) := by
  refine Submodule.mem_inf.2 ⟨mul_mem_pairSpace e₁ e₂ U₁ U₁' U₂ U₂' F c₁ c₂ hF, ?_, fun x => ?_⟩
  · intro u₁ hu₁ u₂ hu₂ x
    have h₁ : e₁ (x * (finGL E a u₁, finGL E b u₂)).1 = e₁ x.1 := f₁.fin_inv x.1 hu₁.2
    have h₂ : e₂ (x * (finGL E a u₁, finGL E b u₂)).2 = e₂ x.2 := f₂.fin_inv x.2 hu₂.2
    show e₁ (x * (finGL E a u₁, finGL E b u₂)).1 * e₂ (x * (finGL E a u₁, finGL E b u₂)).2 *
      F (x * (finGL E a u₁, finGL E b u₂)) = e₁ x.1 * e₂ x.2 * F x
    rw [h₁, h₂, hT.1 u₁ hu₁.1 u₂ hu₂.1 x]
  · have h : (fun k : Kinf E a × Kinf E b =>
        (fun y : H E a b => e₁ y.1 * e₂ y.2 * F y)
          (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
        (e₁ x.1 * e₂ x.2) • fun k : Kinf E a × Kinf E b =>
          F (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) := by
      funext k
      have h₁ : e₁ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).1 = e₁ x.1 :=
        f₁.inf_inv x.1 k.1
      have h₂ : e₂ (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))).2 = e₂ x.2 :=
        f₂.inf_inv x.2 k.2
      simp only [Pi.smul_apply, smul_eq_mul, h₁, h₂]
    rw [h]
    exact Submodule.smul_mem _ _ (hT.2 x)

end PairCarry

end GlobalTheory.CompanionTheory.LimV

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolReOf2T
section
noncomputable section

namespace GlobalTheory.CompanionTheory.ThetaK

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter _root_.Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKF PositivityTheory.HoweDualityUnitaryAlt
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {a a' : ℕ} {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem cmp_finT (hM : MaxFinT) {R R₂ : RealMaps F a a'} {Rf Rf₂ : FinMaps F a a'} (m : IsMatched B G X om om' R Rf)
    (v : Pl F) (n₂ : Nontrivial (Rf₂.Pi v)) (o : (SB _).map (Rf₂.p v) = ⊤) (o' : (SB _).map (Rf₂.p' v) = ⊤)
    (x₁ : Maximal (fun P => GlobalTheory.Published.ThetaSub om v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p v) ⊓ SB _))
    (x₂ : Maximal (fun P => GlobalTheory.Published.ThetaSub om' v P ∧ P ≠ SB _) (LinearMap.ker (Rf₂.p' v) ⊓ SB _))
    (eq₂ : ∀ h ∈ UAt σ G.W (evFin F v), ∀ φ ∈ SB _, ∀ φ' ∈ SB _, ∀ φ₁ ∈ SB _, ∀ φ₁' ∈ SB _,
      Acts (evFin F v) (om (1, h)) φ φ₁ → Acts (evFin F v) (om' (1, h)) φ' φ₁' →
      Rf₂.p v φ = Rf₂.p' v φ' → Rf₂.p v φ₁ = Rf₂.p' v φ₁') :
    ∃ (e : Rf.Pi v →ₗ[ℂ] Rf₂.Pi v) (c : ℂ), c ≠ 0 ∧ (∀ x ∈ SB _, e (Rf.p v x) = Rf₂.p v x) ∧
      ∀ x ∈ SB _, e (Rf.p' v x) = c • Rf₂.p' v x := by
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨ω, ρ, hω⟩ := PositivityTheory.ThKH.Locrep.locRepEx F E σ _ _ B _ _ G.M om
    ⟨p1.base, ⟨_, _, p1.herm⟩, ⟨_, _, p1.skew⟩, p1.good, ⟨_, _, p1.weil⟩⟩ v
  choose A' hA' hA'' using fun (i : UAt σ G.W (evFin F v)) (x : SB (Fin a' × Fin (a + a') → Fv F v)) => ex_fin p2 v i x x.2
  have ac : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)),
      Acts (evFin F v) (om (1, i.1)) x (ω (1, i.1) x) := fun i x => (hω.acts 1 (one_at _) i i.2 x x.2 _).2 rfl
  have pr : ∀ (i : UAt σ G.W (evFin F v)) (x : SB (Fin a × Fin (a + a') → Fv F v)), ω (1, i.1) x ∈ SB _ :=
    fun i x => hω.pres 1 (one_at _) i i.2 x x.2
  haveI := GlobalTheory.AdelicUnitaryTop.properSpace_adicCompletion F v
  haveI : SecondCountableTopology (Fv F v) := inferInstance
  exact schur_match (SB _) (SB _) (Rf.p v) (Rf.p' v) (Rf₂.p v) (Rf₂.p' v) (m.fin.onto v) (m.fin.onto' v) o o'
    (fun x hx => (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).1 _ _ (maxFinP m v).1 x₁) x hx).1)
    (ker_of_eq ((hM F E σ B _ _ G X om om' m.triple v trivial).2 _ _ (maxFinP m v).2 x₂))
    (fun i : UAt σ G.W (evFin F v) => ω (1, i.1) ∘ₗ Submodule.subtype _) A' pr hA'
    (fun i x x' => m.fin.equiv v i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun i x x' => eq₂ i i.2 x x.2 x' x'.2 _ (pr i x) _ (hA' i x') (ac i x) (hA'' i x'))
    (fun N hN => m.fin.irred v N fun h hh x hx y _ e hp => by
      rw [(hω.acts 1 (one_at _) h hh x hx y).1 e]; exact hN ⟨h, hh⟩ ⟨x, hx⟩ hp)
    (rank_SB _)

theorem polRe_of2T (hH : PositivityTheory.ThKR.JoinTri) (hM : MaxFinT) (hO : ArchOp) (hL : ArchLie) (hQ : ArchUniq) (hC : PolCount)
    (hJ : CartanConj) (hV : CartanMove) (hK : KCoinv) (hI : ILeft) : PolRe := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' R Rf m V V' W R₂ Rf₂ m₂ ⟨c₂, hc₂, hc⟩
  have p1 := pairV m.triple
  have p2 := pairV' m.triple
  obtain ⟨h, hh, hh'⟩ := hJ F E σ B _ G.W W _ _ p1.base p1.skew m₂.triple.geo.hW
  obtain ⟨g, hg, hg', hP⟩ := hV F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 V W (reG G V V' W).M rfl (pairV m₂.triple) h hh hh'
  obtain ⟨g', hk, hk', hP'⟩ := hV F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 V' W (reG G V V' W).M' rfl (pairV' m₂.triple) h hh hh'
  obtain ⟨T, hT, -⟩ := hO F E σ B _ _ _ _ _ _ _ om _ _ _ _ p1 g hg h hh
  obtain ⟨T', hT', -⟩ := hO F E σ B _ _ _ _ _ _ _ om' _ _ _ _ p2 g' hk h hh
  obtain ⟨e, c, c0, he, he'⟩ := archimedean_matched_maps_compare hH hO hL hQ hC ⟨m₂.triple, real_trans hO hL hQ m.triple m₂.triple m.real ⟨hg, hg'⟩ ⟨hk, hk'⟩
    ⟨hh, hh'⟩ hT hT' (hP T hT) (hP' T' hT'), m₂.fin⟩ m₂
  choose ef cf cf0 hef hef' using fun v => cmp_finT (R₂ := R₂) hM m v (m₂.fin.nontriv v) (m₂.fin.onto v) (m₂.fin.onto' v)
    (maxFinP m₂ v).1 (maxFinP m₂ v).2 (m₂.fin.equiv v)
  have cf1 : ∀ v ∉ X.T, cf v = 1 := fun v hv => by
    obtain ⟨s1, s2⟩ := m₂.fin.sph v hv
    have x1 := hef v _ (p1.good.vac v).1
    rw [(m.fin.sph v hv).1, hef' v _ (p2.good.vac v).1] at x1
    have x2 : cf v • Rf₂.p v (G.M.vac v) = (1 : ℂ) • Rf₂.p v (G.M.vac v) := by
      rw [one_smul]; exact (congrArg (cf v • ·) s1).trans x1
    exact smul_left_injective ℂ s2 x2
  let Λ : ℂ := c * ∏ v ∈ X.T, cf v
  refine ⟨c₂ * Λ, mul_ne_zero hc₂ (mul_ne_zero c0 (Finset.prod_ne_zero_iff.2 fun v _ => cf0 v)), ?_⟩
  rintro Φ Φ' hΦ' ⟨S, hS, k, k', f, φ, f', φ', h1, h2, rfl, rfl, eq⟩ x
  choose u hu hu' using fun i => (show f i ∈ ((reG G V V' W).M.Pol B.ψ B.emb).map (T : _ →ₗ[ℂ] _) from hP T hT ▸ (h1 i).1)
  choose u' hw hw' using fun i => (show f' i ∈ ((reG G V V' W).M'.Pol B.ψ B.emb).map (T' : _ →ₗ[ℂ] _) from hP' T' hT' ▸ (h2 i).1)
  have e1 := move_sum p1.good hT u φ (fun i => (h1 i).2.1) fun i => ev_of_off (h1 i).2.2
  have e2 := move_sum p2.good hT' u' φ' (fun i => (h2 i).2.1) fun i => ev_of_off (h2 i).2.2
  have fu : ∀ i, T (u i) = f i := hu'
  have fu' : ∀ i, T' (u' i) = f' i := hw'
  simp only [fu] at e1
  simp only [fu'] at e2
  have s1 : ∑ i, pure (u i) (φ i) ∈ schA F _ := sum_mem fun i _ =>
    GlobalTheory.TensUniq.pure_mem_schA _ _ (h1 i).2.1 ((good_std p1.good).congr (ev_of_off (h1 i).2.2))
  have so : ∑ i, pure (u' i) (φ' i) ∈ G.M'.So B.ψ B.τ₁ := by
    have := (hK F E σ B a a' G X om om' R Rf m).2 (g', h)⁻¹ _ hΦ'
    rwa [← e2, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have e3 : Λ • ∑ i, pure (u' i) (φ' i) = ∑ i, pure (Λ • u' i) (φ' i) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => funext fun y => (mul_assoc _ _ _).symm
  have pm : PolMatch B (reG G V V' W) X R₂ Rf₂ (∑ i, pure (u i) (φ i)) (Λ • ∑ i, pure (u' i) (φ' i)) := by
    refine ⟨S, hS, k, k', u, φ, fun i => Λ • u' i, φ', fun i => ⟨hu i, (h1 i).2⟩,
      fun i => ⟨Submodule.smul_mem _ _ (hw i), (h2 i).2⟩, rfl, e3, ?_⟩
    have := congrArg (TensorProduct.map e (PiTensorProduct.map fun v : S => ef v)) eq
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, TensorProduct.map_tmul, PiTensorProduct.map_tprod] at this
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (this.trans (Finset.sum_congr rfl fun j _ => ?_))
    · rw [← fu i, show e (R.p (T (u i))) = R₂.p (u i) from he _ (hu i)]
      simp only [hef _ _ ((h1 i).2.1 _)]
    · rw [← fu' j, show e (R.p' (T' (u' j))) = c • R₂.p' (u' j) from he' _ (hw j)]
      simp only [hef' _ _ ((h2 j).2.1 _)]
      rw [MultilinearMap.map_smul_univ, TensorProduct.smul_tmul_smul, map_smul, TensorProduct.smul_tmul']
      simp only [RingHom.id_apply]
      rw [Finset.prod_coe_sort S cf, ← Finset.prod_subset hS fun v _ hv => cf1 v hv]
  have := hc _ _ (Submodule.smul_mem _ Λ (so_re V V' W so)) pm (x * h)
  rw [← e1, ← e2, I_move hI p1 s1, I_move hI p2 (so_le p2.good _ so), mul_assoc, ← I_smul]
  exact this

end GlobalTheory.CompanionTheory.ThetaK

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionThetaSeriesInvariance
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem finite_contributing : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) → S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ δ : ℝ, 0 < δ →
    {x : F | (∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F) ∧
      phiA G a (fun _ => θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0}.Finite := by
  intro F _ _ _ θ _ S T G g a _ hGc hg hST ha δ hδ
  obtain ⟨N, hN, hNint⟩ := GlobalTheory.T.bounded_denominators_compact_idele_set F {a} isCompact_singleton S (fun v => tsupport (g v))
    (fun v hv => (hg v hv).2)
  have h1 : ((↑a⁻¹ : AF F)).1 * (↑a : AF F).1 = 1 := congrArg Prod.fst (Units.inv_mul a)
  have h2 : θ δ⁻¹ * θ δ = 1 := by rw [← map_mul, inv_mul_cancel₀ hδ.ne', map_one]
  have hcd : ∀ z : Ainf F, θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z)) = z := by
    intro z
    calc θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * ((↑a : AF F).1 * (θ δ * z))
        = θ δ⁻¹ * (((↑a⁻¹ : AF F)).1 * (↑a : AF F).1) * θ δ * z := by ring
      _ = z := by rw [h1, mul_one, h2, one_mul]
  have hK : IsCompact ((fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G) :=
    hGc.image (continuous_const.mul continuous_id)
  choose C hC using fun w : NumberField.InfinitePlace F =>
    hK.exists_bound_of_continuousOn (f := fun z : NumberField.InfiniteAdeleRing F => z w)
      (continuous_apply w).continuousOn
  refine ((NumberField.Embeddings.finite_of_norm_le F ℂ ((N : ℝ) * ∑ w, ‖C w‖)).image
    (fun y => y / (N : F))).subset ?_
  rintro x ⟨hxT, hne⟩
  have hG0 := left_ne_zero_of_mul hne
  have hpsi : ∀ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) x) ≠ 0 :=
    fun v hv => Finset.prod_ne_zero_iff.mp (right_ne_zero_of_mul hne) v hv
  have hS : ∀ v ∈ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ tsupport (g v) := by
    intro v hv
    have h := hpsi v (hST hv)
    simp only [psiA, if_pos hv] at h
    rw [mul_comm]
    exact subset_tsupport _ h
  have hnS : ∀ v ∉ S, algebraMap F (Fv F v) x * (↑a : AF F).2 v ∈ v.adicCompletionIntegers F := by
    intro v hv
    by_cases hvT : v ∈ T
    · have h := hpsi v hvT
      simp only [psiA, if_neg hv] at h
      rw [mul_comm]
      by_contra hc
      exact h (if_neg hc)
    · exact mul_mem (hxT v hvT) (ha v hvT).1
  obtain ⟨y, hy⟩ := hNint a (Set.mem_singleton a) x hS hnS
  have hN0 : (N : F) ≠ 0 := by exact_mod_cast hN.ne'
  have harch : ∀ w : NumberField.InfinitePlace F, w x ≤ C w := by
    intro w
    have hmem : (↑a : AF F).1 * (θ δ * algebraMap F (Ainf F) x) ∈ tsupport G :=
      subset_tsupport _ hG0
    have hx' : algebraMap F (Ainf F) x ∈ (fun z => θ δ⁻¹ * ((↑a⁻¹ : AF F)).1 * z) '' tsupport G :=
      ⟨_, hmem, hcd _⟩
    have hb := hC w _ hx'
    have hn : ‖(algebraMap F (NumberField.InfiniteAdeleRing F) x) w‖ = w x := by
      rw [NumberField.InfiniteAdeleRing.algebraMap_apply, NumberField.InfinitePlace.Completion.norm_coe]
      simp
    rw [← hn]
    exact hb
  have hφ : ∀ φ : F →+* ℂ, ‖φ x‖ ≤ ∑ w, ‖C w‖ := by
    intro φ
    calc ‖φ x‖ = NumberField.InfinitePlace.mk φ x := (NumberField.InfinitePlace.apply φ x).symm
      _ ≤ C (NumberField.InfinitePlace.mk φ) := harch _
      _ ≤ ‖C (NumberField.InfinitePlace.mk φ)‖ := Real.le_norm_self _
      _ ≤ ∑ w, ‖C w‖ := Finset.single_le_sum (f := fun w => ‖C w‖) (fun w _ => norm_nonneg _)
          (Finset.mem_univ _)
  refine ⟨(N : F) * x, ⟨?_, fun φ => ?_⟩, ?_⟩
  · rw [← hy]
    exact NumberField.RingOfIntegers.isIntegral_coe y
  · rw [map_mul, norm_mul, map_natCast, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left (hφ φ) (Nat.cast_nonneg N)
  · field_simp

end GlobalTheory.CompanionTheory.BasePsi
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureFunctionTranslateRayUnits
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

namespace GlobalTheory.CompanionTheory.BasePsi

theorem pure_term : ∀ (F : Type) [Field F] [NumberField F] (θ : ℝ →+* Ainf F) (r : ℝ → (AF F)ˣ), IsRay θ r →
    ∀ (S T : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ), S ⊆ T →
    (∀ v, v ∉ T → (a : AF F).2 v ∈ v.adicCompletionIntegers F ∧ ((a⁻¹ : (AF F)ˣ) : AF F).2 v ∈ v.adicCompletionIntegers F) →
    ∀ (δ : ℝ), 0 < δ → ∀ t : Fˣ,
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) (pr t * (a * r δ)) =
      if ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (phiA G a (fun _ => θ δ * algebraMap F (Ainf F) (t : F)) *
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F))) else 0 := by
  intro F _ _ θ r hr S T G g a hST hT δ hδ t
  obtain ⟨h1, h2⟩ := hr δ hδ
  have c1 : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = (a : AF F).1 * (θ δ * algebraMap F (Ainf F) (t : F)) := by
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).1 = algebraMap F (Ainf F) (t : F) * ((a : AF F).1 * (r δ : AF F).1) := rfl
    rw [this, h1]; ring
  have c2 : ∀ v, ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * algebraMap F (Fv F v) (t : F) := by
    intro v
    have : ((pr t * (a * r δ) : (AF F)ˣ) : AF F).2 v = algebraMap F (Fv F v) (t : F) * ((a : AF F).2 v * (r δ : AF F).2 v) := rfl
    rw [this, h2]
    have h3 : ((1 : FiniteAdeleRing (𝓞 F) F)) v = 1 := rfl
    rw [h3, mul_one, mul_comm]
  have inv : ∀ v, (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v = 1 := by
    intro v
    have : ((a * a⁻¹ : (AF F)ˣ) : AF F).2 v = (a : AF F).2 v * ((a⁻¹ : (AF F)ˣ) : AF F).2 v := rfl
    rw [← this]; simp
  have key : ∀ v, v ∉ T → ((a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F ↔
      algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F) := by
    intro v hv
    constructor
    · intro h
      have h' := mul_mem (hT v hv).2 h
      have e : ((a⁻¹ : (AF F)ˣ) : AF F).2 v * ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          algebraMap F (Fv F v) (t : F) := by
        rw [← mul_assoc, mul_comm (((a⁻¹ : (AF F)ˣ) : AF F).2 v), inv, one_mul]
      rwa [e] at h'
    · exact fun h => mul_mem (hT v hv).1 h
  rw [GlobalTheory.T.pure_adelic_function_formula F S G g (pr t * (a * r δ))]
  simp only [c1, c2]
  by_cases ht : ∀ v, v ∉ T → algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
  · rw [if_pos ht]
    by_cases h : ∀ v, v ∉ S → (a : AF F).2 v * algebraMap F (Fv F v) (t : F) ∈ v.adicCompletionIntegers F
    · rw [if_pos h]
      have hp : ∏ v ∈ S, g v ((a : AF F).2 v * algebraMap F (Fv F v) (t : F)) =
          ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) := by
        rw [← Finset.prod_subset hST]
        · refine Finset.prod_congr rfl fun v hv => ?_
          simp [psiA, hv]
        · intro v _ hv
          simp [psiA, hv, h v hv]
      rw [hp]
      rfl
    · rw [if_neg h]
      push_neg at h
      obtain ⟨v, hvS, hv⟩ := h
      have hvT : v ∈ T := by
        by_contra hvT
        exact hv ((key v hvT).2 (ht v hvT))
      have hz : ∏ v ∈ T, psiA S g a v (fun _ => algebraMap F (Fv F v) (t : F)) = 0 :=
        Finset.prod_eq_zero hvT (by simp [psiA, hvS, hv])
      rw [hz]
      simp
  · rw [if_neg ht, if_neg]
    intro h
    exact ht fun v hv => (key v hv).1 (h v fun hs => hv (hST hs))

end GlobalTheory.CompanionTheory.BasePsi
end

