module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsTopologicalRingAE
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ClassNumberFiniteIntegralLevelClosedSubgroupGL
section
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.ClassFin

theorem classFinite_integralLevel : ∀ (F : Type) [Field F] [NumberField F] (n : ℕ) (S : Set (MvPolynomial (Fin n × Fin n) F)), (∀ (B : Type) [CommRing B] [Algebra F B], (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((1 : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) ∧ (∀ g h : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g * h : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) ∧ ∀ g : GL (Fin n) B, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0) → (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((g⁻¹ : GL (Fin n) (B)) : Matrix (Fin n) (Fin n) (B)) ij.1 ij.2) P = 0)) → ∃ T : Finset (GL (Fin n) (FiniteAdeleRing (𝓞 F) F)), (∀ s ∈ T, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0)) ∧ ∀ x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((x : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) → ∃ γ : GL (Fin n) F, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((γ : GL (Fin n) (F)) : Matrix (Fin n) (Fin n) (F)) ij.1 ij.2) P = 0) ∧ ∃ s ∈ T, ∃ u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F), (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n => ((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧ (∀ i j, (∀ v, (((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v) ∧ (∀ v, ((((u : GL (Fin n) (FiniteAdeleRing (𝓞 F) F))⁻¹ : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) i j : FiniteAdeleRing (𝓞 F) F) v ∈ HeightOneSpectrum.adicCompletionIntegers F v)) ∧ x = Units.map (RingHom.mapMatrix (algebraMap F (FiniteAdeleRing (𝓞 F) F))).toMonoidHom γ * s * u := by
  intro F _ _ n S hS
  classical

  obtain ⟨R, _, _, R₀, _, b, hAP, hred, hb, hint⟩ :=
    _root_.GlobalTheory.AdeleFree.finiteAdele_free F _ (NumberField.RingOfIntegers.basis F)
  obtain ⟨Γ, hΓ, hcorr⟩ := _root_.GlobalTheory.ClassFin.exists_isQGroup_weilRestriction F _ (NumberField.integralBasis F) n S hS
  have hbF : ∀ i, b i = algebraMap F (FiniteAdeleRing (𝓞 F) F) (NumberField.integralBasis F i) := by
    intro i
    rw [hb i, NumberField.integralBasis_apply]
  have hA := hcorr R (FiniteAdeleRing (𝓞 F) F) b hbF
  have hQ := hcorr ℚ F (NumberField.integralBasis F) (fun i => rfl)
  obtain ⟨T₀, hT₀, hdec⟩ := _root_.GlobalTheory.ClassFin.cf_of_isQGroup _ Γ R R₀ hΓ hAP

  let lift : Matrix ((Fin n × _) ⊕ Unit) ((Fin n × _) ⊕ Unit) R → GL (Fin n) (FiniteAdeleRing (𝓞 F) F) :=
    fun s => if h : ∃ g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F),
        (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
          ((g : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
        s = GlobalTheory.ClassFin.emb b g then h.choose else 1
  have hlift : ∀ s ∈ pts Γ R, (∀ P ∈ S, MvPolynomial.aeval (fun ij : Fin n × Fin n =>
      ((lift s : GL (Fin n) (FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F)) ij.1 ij.2) P = 0) ∧
      s = GlobalTheory.ClassFin.emb b (lift s) := by
    intro s hs
    have h := hA.1 s hs
    simp only [lift, dif_pos h]
    exact h.choose_spec
  obtain ⟨hemb1, hembmul, -, hembinj⟩ := _root_.GlobalTheory.ClassFin.EmbHom.emb_hom R (FiniteAdeleRing (𝓞 F) F) _ (Fin n) b
  refine ⟨T₀.image lift, ?_, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.1 ht
    exact (hlift s (hT₀ s hs)).1
  · intro x hx
    obtain ⟨γ₀, hγ₀, s, hs, u₀, hu₀, hu₀int, hx₀⟩ := hdec _ (hA.2 hred x hx)
    obtain ⟨γ, hγS, rfl⟩ := hQ.1 γ₀ hγ₀
    obtain ⟨u, huS, rfl⟩ := hA.1 u₀ hu₀
    obtain ⟨hsS, hsemb⟩ := hlift s (hT₀ s hs)
    have h1 : ∀ i, b.repr 1 i ∈ R₀ := by
      refine (hint 1).1 ?_
      intro v
      exact (HeightOneSpectrum.adicCompletionIntegers F v).one_mem
    have hunits := _root_.GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational.1 R _ _ (Fin n) b R₀ u h1 hu₀int
    refine ⟨γ, hγS, lift s, Finset.mem_image_of_mem lift hs, u, huS, ?_, ?_⟩
    · intro i j
      exact ⟨(hint _).2 (fun k => (hunits i j k).1), (hint _).2 (fun k => (hunits i j k).2)⟩
    · apply hembinj
      simp only [hembmul]
      rw [hx₀, ← hsemb, _root_.GlobalTheory.ClassFin.EmbInt.emb_integral_and_rational.2 F _ (NumberField.integralBasis F) (Fin n) R _ b hbF γ]

end GlobalTheory.ClassFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
section
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix
open GlobalTheory.Member

namespace GlobalTheory.UnRep.Space

theorem finrank_two (D : D7) : Module.finrank D.host.F D.host.E = 2 :=
  Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield D.host.E) D.host.E

theorem isUnA_finHom {D : D7} (V : HSp D) (g : GA D V) : GlobalTheory.UnRep.IsUnA (cF D) V.gramᵀ (finHom V g).1 := by
  intro x y
  rw [GlobalTheory.UnitarySplit.hermA_eq, GlobalTheory.UnitarySplit.hermA_eq]
  exact (GlobalTheory.Member.RatElt.mem_UJ_iff _ _ _).1 (GlobalTheory.UnitarySplit.finHom_mem V g) y x

theorem herm_neg_eq {D : D7} (V : HSp D) (u v : Fin V.rank → D.host.E) :
    herm (-V.gramᵀ) u v = -GlobalTheory.UnRep.hermE (cF D) V.gramᵀ u v := by
  unfold herm GlobalTheory.UnRep.hermE
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  change u a * (-V.gram b a) * cc (v b) = -(u a * V.gram b a * cc (v b))
  ring


set_option maxHeartbeats 1000000 in
theorem exists_rep_suppSplit : ∀ (D : D7) (V : HSp D) (N : ℕ), 0 < N → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ h ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * h * k ∧ FinCong V N k ∧ GlobalTheory.UnRep.SuppSplit (cF D) N (finHom V h).1 := by
  intro D V N hN g
  obtain ⟨e1, -, hfg, hsp, c2, -, c1, gh, gd, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨γ', h', k', u1, u2, u3, hg, hs, hk, -⟩ := GlobalTheory.T.exists_unitary_adelic_decomposition_split_support D.host.F D.host.E (cF D) V.rank V.gramᵀ
    ⟨c2, c1, gh, gd⟩ (finrank_two D) (latC V) hfg hsp (finHom V g) N (isUnA_finHom V g) hN
  obtain ⟨-, -, -, lift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨h, hh, eh⟩ := lift h' u2
  obtain ⟨k, hk', ek⟩ := lift k' u3
  obtain ⟨γ, hγ⟩ := r3 γ' fun u v => by rw [herm_neg_eq, herm_neg_eq, u1]
  have eγ : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := GlobalTheory.Member.RatElt.fin_eq hγ
  have e : finHom V g = finHom V γ * finHom V h * finHom V k := by
    apply Units.ext
    rw [hg, Units.val_mul, Units.val_mul, eγ, eh, ek]
  refine ⟨γ, (r1 γ).2 ⟨γ', hγ⟩, γ⁻¹ * g * k⁻¹ * h⁻¹, ?_, h, hh, k, hk', by group, ?_, ?_⟩
  · change finHom V _ = 1
    simp only [map_mul, map_inv, e]
    group
  · unfold FinCong
    rw [e1, ek]
    exact hk
  · rw [eh]
    exact hs

end GlobalTheory.UnRep.Space
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FockVacuumAnnihilationEquationRealCoordinates
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique

namespace GlobalTheory.VacUnique.Ann

theorem deriv_twisted_line {R : Type} [NormedAddCommGroup R] [NormedSpace ℝ R] (F : R → ℂ) (hF : Differentiable ℝ F)
    (om : R →ₗ[ℝ] R →ₗ[ℝ] ℝ) (w u : R) :
    deriv (fun t : ℝ => Complex.exp (-(Real.pi * Complex.I) * (om w (t • u) : ℂ)) * F (w + t • u)) 0 =
      fderiv ℝ F w u - Real.pi * Complex.I * (om w u : ℂ) * F w := by
  have h1 : HasDerivAt (fun t : ℝ => w + t • u) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add w
  have h2 : HasDerivAt (fun t : ℝ => F (w + t • u)) (fderiv ℝ F w u) 0 := by
    have h := (hF (w + (0 : ℝ) • u)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h1
    simpa [Function.comp_def] using h
  have h3 : HasDerivAt (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ))
      (-(Real.pi * Complex.I) * (om w u : ℂ)) 0 := by
    have e : (fun t : ℝ => -(Real.pi * Complex.I) * (om w (t • u) : ℂ)) =
        fun t : ℝ => (t : ℂ) * (-(Real.pi * Complex.I) * (om w u : ℂ)) := by
      funext t
      rw [LinearMap.map_smul, smul_eq_mul, Complex.ofReal_mul]
      ring
    rw [e]
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const (-(Real.pi * Complex.I) * (om w u : ℂ))
  have h4 := (h3.cexp.mul h2).deriv
  refine Eq.trans h4 ?_
  simp only [zero_smul, map_zero, Complex.ofReal_zero, mul_zero, Complex.exp_zero, add_zero, one_mul]
  ring

variable {D : D7} {θ : InfFam D} {σ : (D.what₂.Tau → ℂ) →+ AE D}

open Classical in
theorem lineAt_eq (h : Chart θ σ) (S T : HSp D) (τ : D.what₂.Tau) (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (t : ℝ) :
    lineAt θ τ z t = iotaW σ T S (t • (Pi.single τ z : RW T S)) := by
  have hL : IsLineAt θ τ z (lineAt θ τ z) :=
    Classical.epsilon_spec (GlobalTheory.RealLineAt.lineAt_exists D θ h.inf T.rank S.rank τ z)
  refine h.real_ext (V := T) (W := S) (hL.2.1 t) (h.real_iota T S _) ?_
  rw [h.pi_iota]
  funext τ'
  refine (hL.2.2 t τ').trans ?_
  by_cases e : τ' = τ
  · subst e
    have e1 : (Pi.single τ' z : RW T S) τ' = z := Pi.single_eq_same _ _
    rw [if_pos rfl, Pi.smul_apply, e1]
    funext i j
    show (t : ℂ) * z i j = t • z i j
    exact (Complex.real_smul).symm
  · have e1 : (Pi.single τ z : RW T S) τ' = 0 := Pi.single_eq_of_ne e _
    rw [if_neg e, Pi.smul_apply, e1, smul_zero]
    rfl

open Classical in
theorem dRho_eq (h : Chart θ σ) {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) (S T : HSp D)
    (f : WO S T → ℂ) (hF : Differentiable ℝ fun z : RW T S => f (iotaW σ T S z)) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) (w : RW T S) :
    Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ z f (iotaW σ T S w) =
      fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (Pi.single τ z) -
        Real.pi * Complex.I * (omO S T w (Pi.single τ z) : ℂ) * f (iotaW σ T S w) := by
  refine Eq.trans ?_ (deriv_twisted_line _ hF (omO S T) w (Pi.single τ z))
  unfold Formalism.IndefR.Datum.dRho
  congr 1
  funext t
  rw [lineAt_eq h S T τ z t]
  unfold heisO
  rw [_root_.GlobalTheory.OrientedChar.char_symplOH D θ ψ h.inf hψ S T _ _ (Or.inl (h.real_iota T S w)), h.pi_iota, h.pi_iota,
    (iotaW σ T S).map_add]

open Classical in
theorem jO_single (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ)
    (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (τ : D.what₂.Tau)
    (z : Matrix (Fin T.rank) (Fin S.rank) ℂ) :
    jO S T sS sT (Pi.single τ z) = Pi.single τ (cplxO (sS τ) (sT τ) z) := by
  funext τ'
  rw [jO_apply]
  by_cases e : τ' = τ
  · subst e
    have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ' y : RW T S) τ' = y :=
      fun _ => Pi.single_eq_same _ _
    rw [e1, e1]
  · have e1 : ∀ y : Matrix (Fin T.rank) (Fin S.rank) ℂ, (Pi.single τ y : RW T S) τ' = 0 :=
      fun _ => Pi.single_eq_of_ne e _
    rw [e1, e1]
    show Complex.I • (sT τ' * (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ) * sS τ') = (0 : Matrix (Fin T.rank) (Fin S.rank) ℂ)
    rw [Matrix.mul_zero, Matrix.zero_mul, smul_zero]

theorem vacuum_annihilation : ∀ (D : D7) (θ : InfFam D) (σ : (D.what₂.Tau → ℂ) →+ AE D), Chart θ σ → ∀ (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (S T : HSp D) (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ) (f : WO S T → ℂ), IsThetaFunO ψ S T f → (∀ τ, IsFockVacAt (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ)) f) → Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) ∧ ∀ w z : RW T S, (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z - Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)) + Complex.I * (fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w (jO S T sS sT z) - Real.pi * Complex.I * (omO S T w (jO S T sS sT z) : ℂ) * f (iotaW σ T S w)) = 0 := by
  classical
  intro D θ σ h ψ hψ S T sS sT f hf hv
  have hF : Differentiable ℝ (fun z : RW T S => f (iotaW σ T S z)) := by
    have h1 := ((smooth_iff_sm_and_real_lines D θ σ h T S).1 f).1 hf.smooth 0
    simp only [zero_add] at h1
    exact h1.differentiable (by simp)
  refine ⟨hF, fun w z => ?_⟩
  let A : RW T S →+ ℂ :=
    { toFun := fun z => fderiv ℝ (fun z : RW T S => f (iotaW σ T S z)) w z -
        Real.pi * Complex.I * (omO S T w z : ℂ) * f (iotaW σ T S w)
      map_zero' := by simp
      map_add' := fun x y => by
        rw [ContinuousLinearMap.map_add (f := _), LinearMap.map_add (f := _), Complex.ofReal_add]
        ring }
  show A z + Complex.I * A (jO S T sS sT z) = 0
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.univ_sum_single z, map_sum, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun τ _ => ?_
  have h1 := congrFun (hv τ (z τ)) (iotaW σ T S w)
  have h2 : Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (z τ) f (iotaW σ T S w) +
      Complex.I * Formalism.IndefR.Datum.dRho (heisO ψ S T) θ τ (cplxO (sS τ) (sT τ) (z τ)) f (iotaW σ T S w) = 0 := h1
  have h3 := dRho_eq h hψ S T f hF τ (z τ) w
  have h4 := dRho_eq h hψ S T f hF τ (cplxO (sS τ) (sT τ) (z τ)) w
  have h5 := jO_single S T sS sT τ (z τ)
  have h6 : A (Pi.single τ (z τ)) + Complex.I * A (Pi.single τ (cplxO (sS τ) (sT τ) (z τ))) = 0 :=
    (congrArg₂ (fun a b : ℂ => a + Complex.I * b) h3 h4).symm.trans h2
  exact (congrArg (fun b => A (Pi.single τ (z τ)) + Complex.I * A b) h5).trans h6

end GlobalTheory.VacUnique.Ann
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenNsmulCompletedHomLatticeFiniteAdelic
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LatOpen

open GlobalTheory.LatVac Topology

theorem isOpen_of_nhds {G G' : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [AddCommGroup G'] (φ : G →+ G') (L : AddSubgroup G) (N : ℕ) (U : Set G) (hU : U ∈ 𝓝 0)
    (h : ∀ x ∈ U, ∃ l ∈ L, φ (x - N • l) = 0) : IsOpen {x : G | ∃ l ∈ L, φ (x - N • l) = 0} := by
  let H : AddSubgroup G :=
    { carrier := {x : G | ∃ l ∈ L, φ (x - N • l) = 0}
      zero_mem' := ⟨0, L.zero_mem, by simp⟩
      add_mem' := by
        rintro x y ⟨l, hl, e⟩ ⟨l', hl', e'⟩
        refine ⟨l + l', L.add_mem hl hl', ?_⟩
        rw [show x + y - N • (l + l') = (x - N • l) + (y - N • l') by rw [nsmul_add]; abel, map_add (f := _), e, e', add_zero]
      neg_mem' := by
        rintro x ⟨l, hl, e⟩
        refine ⟨-l, L.neg_mem hl, ?_⟩
        rw [show -x - N • (-l) = -(x - N • l) by rw [neg_nsmul]; abel, map_neg, e, neg_zero] }
  exact H.isOpen_of_mem_nhds (g := 0) (Filter.mem_of_superset hU h)

theorem isOpen_intAf (F : Type) [Field F] [NumberField F] : IsOpen (intAf F) :=
  RestrictedProduct.isOpen_forall_mem (A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F)))
    fun v => Valued.isOpen_valuationSubring _

theorem zero_mem_intAf (F : Type) [Field F] [NumberField F] : (0 : Af F) ∈ intAf F :=
  fun v => zero_mem (v.adicCompletionIntegers F)

variable {D : D7}

theorem finPart_eq_sum {ι : Type} [Fintype ι] (b : Module.Basis ι D.host.F D.host.E) (z : AE D) :
    finPart D z = ∑ k, sndA D.host.F ((Algebra.TensorProduct.basis (AF D.host.F) b).coord k z) ⊗ₜ[D.host.F] b k := by
  conv_lhs => rw [← (Algebra.TensorProduct.basis (AF D.host.F) b).sum_repr z]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [show ∀ y, finPart D y = (finPart D).toAddMonoidHom y from fun _ => rfl, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  show finPart D _ = _
  rw [Algebra.TensorProduct.basis_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  rfl

theorem nsmul_tmul_cancel {F A E : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A] [AddCommGroup E] [Module F E]
    {N M : ℕ} (hN : 0 < N) (hM : 0 < M) (a : A) (e : E) :
    N • ((algebraMap F A ((N * M : ℕ) : F)⁻¹ * a) ⊗ₜ[F] (M • e)) = a ⊗ₜ[F] e := by
  have hN' : (N : F) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  have hM' : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  rw [← Algebra.smul_def, ← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F, TensorProduct.tmul_smul,
    ← TensorProduct.smul_tmul', smul_smul, smul_smul, Nat.cast_mul, mul_inv_cancel₀ (mul_ne_zero hN' hM'), one_smul]

private theorem selfDual_isFullLattice {D : D7} : ∀ (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)),
    IsSelfDualC V Λ → Submodule.IsFullLattice D.host.E Λ := by
  intro V Λ hΛ
  haveI : Submodule.IsLattice D.host.E Λ := hΛ.1
  refine ⟨?_⟩
  obtain ⟨s, hs⟩ := hΛ.1.fg
  apply eq_top_iff.mpr
  intro y _
  let f : (Fin V.rank → D.host.E) → D.host.E := fun x =>
    ∑ i, ∑ j, star (x i) * V.gram i j * y j
  obtain ⟨a, ha⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E)) s f
  have ha0 : (algebraMap (𝓞 D.host.E) D.host.E a) ≠ 0 := by
    exact (FaithfulSMul.algebraMap_injective _ _).ne (mem_nonZeroDivisors_iff_ne_zero.mp a.2)
  let P : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E) := {
    carrier := {x | ∃ b : 𝓞 D.host.E, (b : D.host.E) = (algebraMap (𝓞 D.host.E) D.host.E a) * f x}
    zero_mem' := by refine ⟨0, ?_⟩; simp [f]
    add_mem' := by
      rintro x z ⟨b, hb⟩ ⟨c, hc⟩
      refine ⟨b + c, ?_⟩
      change (b : D.host.E) + c = _
      rw [hb, hc]
      simp [f, map_add, add_mul, Finset.sum_add_distrib, mul_add]
    smul_mem' := by
      rintro c x ⟨b, hb⟩
      refine ⟨RingOfIntegers.mapRingHom (starRingEnd D.host.E) c * b, ?_⟩
      simp only [map_mul, hb, f, Pi.smul_apply, Algebra.smul_def, map_mul, RingOfIntegers.mapRingHom_apply, star_mul]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      change star (c : D.host.E) * _ = _
      ring }
  have hsP : (s : Set (Fin V.rank → D.host.E)) ⊆ P := by
    intro x hx
    obtain ⟨b, hb⟩ := ha x hx
    exact ⟨b, by simpa [Algebra.smul_def] using hb⟩
  have hy : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Λ := by
    apply (hΛ.2 _).2
    intro x hx
    have hxP : x ∈ P := (hs ▸ Submodule.span_le.mpr hsP) hx
    obtain ⟨b, hb⟩ := hxP
    refine ⟨b, ?_⟩
    rw [hb]
    dsimp only [f, Pi.smul_apply]
    simp only [smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hy' : (algebraMap (𝓞 D.host.E) D.host.E a) • y ∈ Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E)) :=
    Submodule.subset_span hy
  have := (Submodule.span D.host.E (Λ : Set (Fin V.rank → D.host.E))).smul_mem
    (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ hy' 
  change (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹ •
    ((algebraMap (𝓞 D.host.E) D.host.E a) • y) ∈ _ at this
  rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ ha0, one_smul] at this
  exact this


theorem isOpen_nsmul_latO : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ N : ℕ, 0 < N → IsOpen {x : WO S T | ∃ l ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True), (x - N • l).map (finPart D) = 0} := by
  intro D S T ΛS ΛT hS hT N hN
  classical
  let b := Module.finBasis D.host.F D.host.E
  let B := Algebra.TensorProduct.basis (AF D.host.F) b
  choose M hM hMl using fun p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) =>
    GlobalTheory.T.scaled_matrix_mem_rational_lattice D S T ΛS ΛT (selfDual_isFullLattice S ΛS hS) (selfDual_isFullLattice T ΛT hT) (Matrix.single p.1 p.2.1 (b p.2.2))
  let f : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E) → WO S T → Af D.host.F := fun p x =>
    algebraMap D.host.F (Af D.host.F) ((N * M p : ℕ) : D.host.F)⁻¹ * sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1))
  have hf : ∀ p, Continuous (f p) := fun p => by
    have h1 : Continuous (B.coord p.2.2) := IsModuleTopology.continuous_of_linearMap _
    have h2 : Continuous (sndA D.host.F) := continuous_snd
    exact continuous_const.mul (h2.comp (h1.comp ((continuous_apply p.2.1).comp (continuous_apply p.1))))
  have hf0 : ∀ p, f p 0 = 0 := fun p => by
    show _ * sndA D.host.F (B.coord p.2.2 0) = 0
    rw [LinearMap.map_zero, map_zero, mul_zero]
  let φ : WO S T →+ Matrix (Fin T.rank) (Fin S.rank) (Af D.host.F ⊗[D.host.F] D.host.E) :=
    (finPart D).toAddMonoidHom.mapMatrix
  refine isOpen_of_nhds φ _ N (⋂ p, f p ⁻¹' intAf D.host.F) ?_ ?_
  · refine Filter.iInter_mem.2 fun p => ((isOpen_intAf _).preimage (hf p)).mem_nhds ?_
    show f p 0 ∈ intAf D.host.F
    rw [hf0]; exact zero_mem_intAf _
  · intro x hx
    refine ⟨∑ p, finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)),
      AddSubgroup.sum_mem _ fun p _ => finTens_mem_latO (Set.mem_iInter.1 hx p) (hMl p), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [AddMonoidHom.map_sub, AddMonoidHom.map_nsmul, sub_eq_zero, map_sum, ← Finset.sum_nsmul]
    ext i j
    rw [Matrix.sum_apply]
    have e : ∀ p : Fin T.rank × Fin S.rank × Fin (Module.finrank D.host.F D.host.E),
        (N • φ (finTens (f p x) (M p • Matrix.single p.1 p.2.1 (b p.2.2)))) i j =
        sndA D.host.F (B.coord p.2.2 (x p.1 p.2.1)) ⊗ₜ[D.host.F] (Matrix.single p.1 p.2.1 (b p.2.2) i j) :=
      fun p => nsmul_tmul_cancel hN (hM p) _ _
    rw [Finset.sum_congr rfl fun p _ => e p, Fintype.sum_prod_type, Finset.sum_eq_single i, Fintype.sum_prod_type,
      Finset.sum_eq_single j]
    · simp only [Matrix.single_apply_same]
      exact finPart_eq_sum b (x i j)
    · intro j' _ hj
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_col_ne _ _ hj, TensorProduct.tmul_zero]
    · simp
    · intro i' _ hi
      exact Finset.sum_eq_zero fun k _ => by
        rw [Matrix.single_apply_of_row_ne hi, TensorProduct.tmul_zero]
    · simp

end GlobalTheory.LatOpen

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ScaledFiniteMatrixMemLatticeStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FockCompare GlobalTheory.VacUnique
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scaled_finite_matrix_mem_lattice : ∀ (D : D7) (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsFullLattice D.host.E ΛS → Submodule.IsFullLattice D.host.E ΛT → ∀ γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ N : ℕ, 0 < N ∧ N • finRat S T γ ∈ (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) := by
  first
  | exact GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem
  | intro D S T ΛS ΛT hS hT γ
    exact GlobalTheory.VacUnique.Den.exists_nsmul_finRat_mem D S T ΛS ΛT
      hS.toIsLattice hT.toIsLattice γ
end

