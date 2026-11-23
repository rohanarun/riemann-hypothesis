module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.OrdVan2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0010
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0012
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroKIface
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0006
public import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.Bundle0005
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.LocOrdFlag
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
section SlopeTestRemainingChoices
open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
private theorem ine_normal (σ : ↥(Weil h)) (s : ↥(Ine (F := F) A)) : ∃ t, σ * ineIncl h s = ineIncl h t * σ := by
  have : deg (σ * ineIncl h s * σ⁻¹) = 0 := by simp
  refine ⟨⟨_, deg_eq_zero_iff.1 this⟩, ?_⟩
  have e : ineIncl h ⟨_, deg_eq_zero_iff.1 this⟩ = σ * ineIncl h s * σ⁻¹ := rfl
  rw [e, inv_mul_cancel_right]
private theorem core0 {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
    (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (P : LocPrime l) {L : FinExt l} {V : Type}
    [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V]
    (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V) (hV : IsPst P ρ) {n : ℕ} (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → ∃ s, μ j (ineIncl h s) ≠ μ k (ineIncl h s))
    (hP : ∀ σ, (wdPst P ι Bw h hj ρ).charPol σ = ∏ j, (X - C (μ j σ : ℂ))) :
    wdN P ι ρ = 0 ∧ ∀ j, μ j = 1 → ∃ z : ↥(Dpst P ρ), z ≠ 0 ∧ phiD P ρ z = z ∧ ∀ g, actD P ρ g z = z := by
  haveI := hV.finite
  have hc : ∀ σ, (wdRho P ι Bw h hj ρ σ).charpoly = ∏ j, (X - C (μ j σ : ℂ)) :=
    fun σ => (DpstMap.charPol_wdPst P ι Bw h hj ρ hV σ).symm.trans (hP σ)
  obtain ⟨hN, hL⟩ := UpperTheory.inertia_eigenvector_extends_of_distinct_characters (ineIncl h) (wdRho P ι Bw h hj ρ) μ
    (ine_normal h) (isSmooth_wdRho P ι Bw h hj ρ).finite_range hc hμ
  refine ⟨hN _ (isNilpotent_wdN P ι ρ) fun s => ?_, fun j hj1 => ?_⟩
  · have := wdRho_wdN P ι Bw h hj ρ (ineIncl h s)
    rw [deg_ineIncl, zpow_zero, one_smul] at this
    exact this
  obtain ⟨h1, h2⟩ := hL j
  simp only [hj1, MonoidHom.one_apply, Units.val_one, one_smul] at h1 h2
  obtain ⟨h3, h4⟩ := UpperTheory.exists_invariant_vector_of_finite_image_averaging ι h Bw hj P ρ h1 h2
  exact UpperTheory.exists_frobenius_fixed_period h Bw hj P ρ h3 h4
private theorem core (hB : DeRhamPotSemistable) {n : ℕ} (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l))
    (hr : Continuous r) (HT : (F →+* Qbar l) → Multiset ℤ) (μ : Fin n → ↥(Weil h) →* ℂˣ)
    (hμ : ∀ j k, j ≠ k → ∃ s, μ j (ineIncl h s) ≠ μ k (ineIncl h s))
    (hD : DRat ι h r HT fun s => ∏ j, (X - C (μ j s : ℂ)))
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O)
    (hj : GlobalTheory.Pst.Induces Bw) :
    IsPotCrysAt (UpperTheory.V.Loc.PP l) Bw r ∧ ∀ j, μ j = 1 → (∀ τ, ∀ c ∈ HT τ, 0 ≤ c) →
      ∃ v : Fin n → Qbar l, v ≠ 0 ∧ ∀ g, (r g : Matrix (Fin n) (Fin n) (Qbar l)) *ᵥ v = v := by
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨hd, hJ, hP⟩ := hD O Bw hj
  have hp := hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
  obtain ⟨L, r', hm, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hp
  obtain ⟨hN0, hz⟩ := core0 ι h Bw hj (UpperTheory.V.Loc.PP l) (Bw.repE L r') hV μ hμ fun σ =>
    (congrArg (fun x => WD.charPol x σ) e).symm.trans (hP σ)
  refine ⟨(GlobalTheory.PstLaws.wdParameterAt_monodromy_zero_iff_potCrystalline Bw h hj _ ι r hp).1 ?_, fun j hj1 hHT => ?_⟩
  · rw [e]
    exact (mono0_wdPst ι Bw h hj hV).2 hN0
  obtain ⟨z, z0, z1, z2⟩ := hz j hj1
  have hd' := (hm.isdRAt_iff _).1 hd
  have hM := (GlobalTheory.PstLaws.wdN_eq_zero_iff (UpperTheory.V.Loc.PP l) (Bw.repE L r') ι).1 hN0
  have hmult : ∀ (τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥L.1) (c : ℤ), c < 0 → Bw.multE (UpperTheory.V.Loc.PP l) L r' τ' c = 0 := by
    intro τ' c hc0
    let τ : F →+* Qbar l := ((algebraMap ↥L.1 (Om l)).comp τ'.toRingHom).comp
      ((Bw.j.comp (algebraMap F Ω)).codRestrict Bw.Kw.1 Bw.j_E)
    have hτ : IsInduced Bw τ τ' := fun _ => rfl
    have := IsJumpsAt.count_eq _ hm hτ (hJ τ L τ' hτ) c
    rw [Multiset.count_eq_zero.2 fun hc' => absurd (hHT τ c hc') (not_le.2 hc0)] at this
    exact this.symm
  obtain ⟨v, v0, hv⟩ := UpperTheory.exists_invariant_of_dpst_phi_fixed_of_nonneg_weights (fun τ x => hm.1 (Bw.LL_split τ x)) (Bw.repE L r')
    (finiteDimensional_DdR _ _ hd') hmult z z0 (LinearMap.congr_fun hM z) z1 z2
  refine ⟨fun i => (v i : Om l), fun h0 => v0 (funext fun i => Subtype.ext (congrFun h0 i)), fun g => ?_⟩
  have h5 : (r' g : Matrix (Fin n) (Fin n) ↥L.1) *ᵥ v = v := by
    have := hv (Bw.e g)
    rw [← Bw.e.symm_apply_apply g]
    exact this
  funext i
  have h6 := congrArg (algebraMap ↥L.1 (Om l)) (congrFun h5 i)
  rw [RingHom.map_mulVec] at h6
  rw [← hm.2]
  exact h6
omit [IsAlgClosure F Ω] in
private theorem ordChar_inv {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} {ω : (w.adicCompletion F)ˣ →* ℂˣ}
    {hh : (F →+* Qbar l) → ℤ} {ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ} (H : OrdChar ι a ω hh ψ) :
    OrdChar ι a ω⁻¹ (-hh) ψ⁻¹ := by
  refine ⟨?_, H.cont.inv, ?_⟩
  · have hsmooth := H.smooth
    unfold GlobalTheory.SmGL.IsSmoothChar at hsmooth ⊢
    convert hsmooth using 1
    ext x
    simp
  · intro s g hg hs
    have := H.val s g hg hs
    simp only [MonoidHom.comp_apply, Units.coeHom_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val] at this ⊢
    rw [this, mul_inv, map_inv₀]
    congr 1
    unfold algPow
    rw [← finprod_inv_distrib]
    simp
end SlopeTestRemainingChoices
section Main
open GlobalTheory.Pst Polynomial Module Matrix Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N
variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]
  (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w)
private noncomputable def twR {H k : Type} [Group H] [Field k] {n : ℕ} (μ : H →* kˣ) (r : H →* GL (Fin n) k) : H →* GL (Fin n) k where
  toFun g := ⟨(μ g : k) • (r g : Matrix (Fin n) (Fin n) k), (μ g⁻¹ : k) • (r g⁻¹ : Matrix (Fin n) (Fin n) k),
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp,
    by rw [smul_mul_smul_comm, ← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]; simp⟩
  map_one' := Units.ext (by simp)
  map_mul' g g' := Units.ext (by simp [smul_smul, mul_comm])
private theorem twR_cont {H k : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {n : ℕ} {μ : H →* kˣ} {r : H →* GL (Fin n) k}
    (hμ : Continuous μ) (hr : Continuous r) : Continuous (twR μ r) :=
  Units.continuous_iff.2 ⟨(Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr),
    ((Units.continuous_val.comp hμ).smul (Units.continuous_val.comp hr)).comp continuous_inv⟩
private theorem flag (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hw : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal)
    {a : ↥(Weil h) →* (w.adicCompletion F)ˣ} (ha : IsLocalArtin h a) (n : ℕ) :
    ∀ (r : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)), Continuous r →
    ∀ (hh : Fin n → (F →+* Qbar l) → ℤ), (∀ τ, StrictMono fun j => hh j τ) →
    ∀ (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → ↥(Dec (F := F) A) →* (Qbar l)ˣ),
      (∀ j, OrdChar ι a (ω j) (hh j) (ψ j)) →
      (∀ i j, i ≠ j → ∃ s, ω i (a (ineIncl h s)) ≠ ω j (a (ineIncl h s))) →
      DRat ι h r (fun τ => Finset.univ.val.map fun j => hh j τ) (fun s => ∏ j, (X - C (ω j (a s) : ℂ))) →
      HasFlag r ψ := by
  have hB := hL.aut.berger
  induction n with
  | zero => exact fun r _ _ _ _ _ _ _ _ => ⟨1, fun _ => ⟨fun i => i.elim0, fun i => i.elim0⟩⟩
  | succ n ih =>
    intro r hr hh hmono ω ψ hO hne hD
    have hO' := ordChar_inv ι h (hO 0)
    have hc := twR_cont hO'.cont hr
    have h1 := UpperTheory.deRham_rational_twist_by_character hB ι h r (twR (ψ 0)⁻¹ r) (ψ 0)⁻¹ hr hc hO'.cont (fun _ => rfl) _ _ _ _ hD
      (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ hO').1
    obtain ⟨LL, Bw, hj⟩ := GlobalTheory.Pst.Test.exists_induces (l := l) (E := F) (Ω := Ω) hw h
    obtain ⟨v, v0, hv⟩ := (core ι h hB _ hc _ (fun j => (ω j * (ω 0)⁻¹).comp a)
      (fun j k hjk => (hne j k hjk).imp fun s hs e => hs (mul_right_cancel e))
      (by simpa only [MonoidHom.comp_apply, MonoidHom.mul_apply, Units.val_mul] using h1) Bw hj).2 0
      (by rw [mul_inv_cancel]; rfl) (fun τ c hc => by
        simp only [Multiset.mem_map, Finset.mem_val, Finset.mem_univ, true_and, Pi.neg_apply] at hc
        obtain ⟨_, ⟨j, rfl⟩, rfl⟩ := hc
        have := (hmono τ).monotone (Fin.zero_le j)
        omega)
    have hv' : ∀ g, (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l)) *ᵥ v = (ψ 0 g : Qbar l) • v := fun g => by
      have := hv g
      change ((((ψ 0 g)⁻¹ : (Qbar l)ˣ) : Qbar l) • (r g : Matrix (Fin (n + 1)) (Fin (n + 1)) (Qbar l))) *ᵥ v = v at this
      rw [Matrix.smul_mulVec] at this
      rw [← congrArg (fun x => (ψ 0 g : Qbar l) • x) this, smul_smul, Units.mul_inv, one_smul]
    obtain ⟨p, r₁, r', e₁, c₁, c', b1, b2, b3, hfl⟩ := UpperTheory.exists_common_eigenline r ψ v hr v0 hv'
    have h2 := UpperTheory.deRhamRational_of_conj hB ι h r r₁ p hr e₁ _ _ hD
    refine hfl (ih r' c' (fun j => hh j.succ) (fun τ => (hmono τ).comp Fin.strictMono_succ) (fun j => ω j.succ) _
      (fun j => hO j.succ) (fun i j hij => hne _ _ fun e => hij (Fin.succ_injective _ e)) ?_)
    refine UpperTheory.deRham_rational_of_extension_by_character hB ι h r₁ r' (ψ 0) c₁ b1 b2 b3 (hh 0) _ _ _ ?_
      (_root_.UpperTheory.V.Loc.hecke_char_de_rham_of_local_artin_above_l hL h hw ι a ha _ _ _ (hO 0)).1
    convert h2 using 2
    · rw [Fin.univ_val_map, Fin.univ_val_map, List.ofFn_succ, Multiset.cons_coe]
    · rw [Fin.prod_univ_succ]
end Main
theorem UpperTheory.V.Loc.ordFlag_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → OrdFlag := by
  intro hL F Ω _ _ _ _ _ l _ _ ι n w hw A h a ha r hr hh hmono ω ψ hO hne hD
  have hne' : ∀ i j, i ≠ j → ∃ s, ω i (a (ineIncl h s)) ≠ ω j (a (ineIncl h s)) := fun i j hij => by
    obtain ⟨⟨y, hy⟩, hy'⟩ := hne i j hij
    obtain ⟨σ, rfl⟩ := ha.surj y
    have h0 := ha.ord_eq σ
    rw [GlobalTheory.SmGL.ord_eq_zero hy, eq_comm, neg_eq_zero, deg_eq_zero_iff] at h0
    exact ⟨⟨σ, h0⟩, hy'⟩
  exact ⟨flag ι h hL hw ha n r hr hh hmono ω ψ hO hne' hD, fun O _ _ _ Bw hj =>
    (core ι h hL.aut.berger r hr _ (fun j => (ω j).comp a) hne' hD Bw hj).1⟩
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdVan2
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open UpperTheory.V.HV GlobalTheory.GalOfCusp
namespace UpperTheory.V.Th
def OrdVan2Alt : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (ι : Qbar l ≃+* ℂ)
    (x : B.Pt) (h : s.Wt n) (ρ : V.frame.G₀ →* GL (Fin n) (Qbar l)) (P : GL (Fin n) (Qbar l)), V.S' = s.S → 2 ≤ n → n ≤ 4 →
    r.V0ok → x.Arith h → x.D = GDet.ofRep (mat ρ) → Continuous ρ → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (ρ.comp V.pr) →
    Submodule.span (Qbar l) (Set.range (mat ρ)) = ⊤ → V.frame.IsForm c.O n ρ P → (∀ g ∈ V.frame.I0, ρ g = 1) →
    (∀ (v : Vl l L) i j, x.psi v i ≠ x.psi v j * (cycBar L Ω l).comp (Dec (F := L) (s.A v)).subtype) →
    RegDet V.frame c.O ρ P → ∀ z, IsOrdCoc V.frame ρ P r.Ip x.psi z → ∃ Y, ∀ g, z g = dY V.frame (mat ρ) Y g
end UpperTheory.V.Th
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrDesc
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.Pr
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
def AutPtAlt (k : GalLink η Ψ σ g₁ B M L Φ) (n : ℕ) (ι : Qbar l ≃+* ℂ) (ka : G L Ω →* (Qbar l)ˣ) : Prop :=
  ∀ (A : Subalgebra c.O (PadicAlgCl l)) [IsDiscreteValuationRing A] [Module.Finite c.O A] [IsLocalHom (algebraMap c.O A)]
    (ρ : Fr.NRep Φ n A), IsLiftA c.O ρ →
    (∀ v i, ∀ g ∈ Φ.Iv v, (ρ.ψ v i g).val = algebraMap c.O A (Ψ (k.j v g) ^ Fr.w n i).val) →
    ∀ r : G L Ω →* GL (Fin n) (Qbar l), (∀ s, (r s).val = (ρ.r (k.p0 s)).map A.val) → IsIrr r → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι (tw r ka)
end
end UpperTheory.V.Pr
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypeDataOfSTy
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC UpperTheory.V.Af
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix UpperTheory.TNZ
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.NonzeroTypeTheory
abbrev _root_.UpperTheory.NonzeroTypeTheory.typeData_of_s_ty : Prop := ∀ (P : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (a1 : ArtinTransferDecompositionCharacter) (a3 : LocalArtinCharacterProduct) (a4 : FiniteDimensionalTranslationCoordinates) (a5 : TwistedSphericalRepresentative) (a6 : DistinctOnUnitsDistinctOnInertia)
    (a7 : SmoothVectorsFixedByCongruence) (gm : _root_.UpperTheory.TNZ.GMainAlt) (ge : GEmb) (gi : ArtinInertiaProp) (cm : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → Need_CMain) (cp : Need_CProps) (gr : Need_Grp),
    _root_.UpperTheory.NonzeroTypeTheory.TypeDataAlt
end UpperTheory.NonzeroTypeTheory
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroCTop
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped Classical
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
variable {n : ℕ} (G : Grp k n)
theorem cMain_alt (hcb : CompactConductorBasicProp (k := k)) (hccB : G.CompactConductorBoundProp) (hJone : G.JacquetOneProp) (hJmul : G.JacquetMultiplicativeProp)
    (hJinv : G.JacquetInverseProp) (hKC : G.CompactOpenKernelProp) (hΔU : G.ModulusOnUnitsProp) (hΔM : G.ModulusMultiplicativeProp) (hlM : G.LambdaMultiplicativeProp)
    (hlB : G.LambdaBasicProp) (hlU : G.LambdaUnipotentProp) (hiw : G.IwahoriDecompositionProp) (hPJ : G.ParabolicJacquetProp) (hkill : G.AnnihilationProp)
    (hni : G.NonIntegralProp) (hTE : G.TorusCentreEigenProp) (hTp : G.TorusPowerProp) (hjK : G.JacquetKernelProp) (hTI : G.TorusCentreInjectiveProp)
    (hun : UniformizerProp (k := k)) (hlL : LeviSubgroupRestriction) (hjI : G.JacquetImageProp) (hjP : G.Step_jacProd_alt) : G.CMainForAlt := by
  intro L V _ _ π hs hirr ⟨x, hx0, hx⟩
  refine hjP L V π hs hirr ⟨_, G.jac_ne_zero hcb hccB hJone hJmul hJinv hKC hΔU hΔM hlM hlB hlU hiw hPJ hkill hni hTE hTp
    hjK hTI hun π hs x hx0 hx, fun m hm => hjI hlL hJone V π x hx m hm⟩
end Grp
end UpperTheory.TNZ
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroGTop
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.TNZ
theorem gMain_alt (h1 : DeterminantVectorProp) (h2 : UnramifiedTwistProp) (h3 : SumOverListProp) (h4a : IsotypicComponentProp)
    (h4b : ScalarOnInertiaProp) (h5 : SphericalOfUnramifiedProp) (h5' : SphericalUnramifiedProp) (h6 : TwistRestrictionProp) (h6' : UntwistRestrictionProp)
    (h7 : ProductRestrictionProp) (h8a : _root_.UpperTheory.TNZ.Step_cuspSupp_alt) (h8b : _root_.UpperTheory.TNZ.Step_prodIrr_alt) (h9 : ArtinInertiaProp) : _root_.UpperTheory.TNZ.GMainAlt := by
  intro E Ω _ _ _ _ _ A w h a ha ε rc hL hLit s d η hη hdist x hd
  have hψ : ∀ b, IsSmooth ((η b).comp a) := fun b => ha.smooth (hη b)
  constructor
  · rintro ⟨h0, hc⟩
    obtain ⟨v, hv, hsum⟩ := h4a E Ω A w h (rc x) s d (fun b => (η b).comp a) hψ hdist h0 hc
    have hv' : ∀ b, ∃ v' : WD h, v'.unr ∧ v'.lpDim = d b ∧
        v b = v'.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨v', hu, hdim, he⟩ := h4b E Ω A w h (v b) ((η b).comp a) (hψ b) (hv b).1
        (fun t => by rw [(hv b).2.1]; exact (hv b).2.2 t)
      exact ⟨v', hu, hdim.trans (hv b).2.1, he⟩
    choose v' hu hdim he using hv'
    choose Xs instA instM σ hs hi hsph hrc using fun b => h5 E Ω A w h a ha ε rc hL (d b) (v' b) (hu b) (hdim b)
    letI := instA
    letI := instM
    choose hs' hi' hrc' using fun b => h6 E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
    have hdet : ∀ b, HasDetVec (twist (σ b) (detChar (Fin (d b)) (η b))) (η b) :=
      fun b => (h1 _ (d b) (Xs b) (σ b) (η b)).1 (hsph b)
    have hdistU : ∀ b c, b ≠ c → ∃ u : (w.adicCompletion E)ˣ,
        valuation (w.adicCompletion E) (u : w.adicCompletion E) = 1 ∧ η b u ≠ η c u := by
      intro b c hbc
      obtain ⟨t, ht⟩ := hdist b c hbc
      exact ⟨a (ineIncl h t), (h9 E Ω A w h a ha).1 t, ht⟩
    have hI := h8b h8a hLit _ s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' η hη hdet hdistU
    have hrcP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs (fun b => twist (σ b) (detChar (Fin (d b)) (η b))) hs' hi' hI
    have heq : rc (IrrGL.of (multiProd (stdBlocks d hd) fun b => twist (σ b) (detChar (Fin (d b)) (η b)))
        (isSmooth_parInd _ _) hI) = rc x := by
      rw [hrcP, hsum]
      congr 1
      refine List.ofFn_inj.2 (funext fun b => ?_)
      rw [hrc' b, hrc b, he b]
    have e2 := (hL.bij.1 heq).trans (IrrGL.of_rep x).symm
    obtain ⟨e⟩ := IrrGL.of_eq_of.1 e2
    exact ⟨Xs, instA, instM, fun b => twist (σ b) (detChar (Fin (d b)) (η b)), hs', hi', hdet, ⟨e.symm⟩⟩
  · rintro ⟨Xs, instA, instM, σ, hs, hi, hdet, ⟨e⟩⟩
    letI := instA
    letI := instM
    have hI : (multiProd (stdBlocks d hd) σ).IsIrreducible := GlobalTheory.Parabolic.isIrreducible_of_equiv e x.2.rep.irr
    have hx : x = IrrGL.of (multiProd (stdBlocks d hd) σ) (isSmooth_parInd _ _) hI :=
      (IrrGL.of_rep x).symm.trans (IrrGL.of_eq_of.2 ⟨e⟩)
    have hfac : ∀ b, ∃ u : WD h, u.unr ∧ u.lpDim = d b ∧
        rc (IrrGL.of (σ b) (hs b) (hi b)) = u.lpChar (WD.lpOfChar h ((η b).comp a) (hψ b)) := by
      intro b
      obtain ⟨hs', hi', hr⟩ := h6' E Ω A w h a ha ε rc hL (d b) (Xs b) (σ b) (hs b) (hi b) (η b) (hη b)
      exact ⟨_, h5' E Ω A w h a ha ε rc hL (d b) (Xs b) _ hs' hi' ((h1 _ (d b) (Xs b) (σ b) (η b)).2 (hdet b)),
        hL.dim _, hr⟩
    choose u hu hud hur using hfac
    have hl := h3 E Ω A w h (List.ofFn fun b => rc (IrrGL.of (σ b) (hs b) (hi b)))
    have hP := h7 E Ω A w h a ha ε rc hL s x.1 d hd Xs σ hs hi hI
    rw [← hx] at hP
    rw [hP]
    refine ⟨hl.1.2 fun y hy => ?_, fun t => ?_⟩
    · simp only [List.mem_ofFn, Set.mem_range] at hy
      obtain ⟨b, rfl⟩ := hy
      rw [hur b]
      exact (h2 E Ω A w h (u b) _ (hψ b) (hu b)).1
    · rw [hl.2, List.map_ofFn, List.prod_ofFn]
      refine Finset.prod_congr rfl fun b _ => ?_
      simp only [Function.comp_apply]
      rw [hur b, (h2 E Ω A w h (u b) _ (hψ b) (hu b)).2 t, hud b]
      rfl
end UpperTheory.TNZ
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPCuspSupp
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ.CuspidalSupport₂
variable {k : Type} [Field k]
end UpperTheory.TNZ.CuspidalSupport₂
namespace UpperTheory.TNZ
open CuspidalSupport₂ in
theorem step_cuspSupp_alt : _root_.UpperTheory.TNZ.Step_cuspSupp_alt := by
  intro hL k _ _ _ _ d X _ _ σ hs hi η hη hdv
  obtain ⟨v, hv0, hv⟩ := hdv
  set τ := twist σ (detChar (Fin d) η⁻¹) with hτ
  have hτs : IsSmooth τ := isSmooth_twist hs hη.inv.detChar
  have hτi : τ.IsIrreducible := isIrreducible_twist hi _
  have hadm : IsAdmissible τ := (hL.bz k).1 (Fin d) X τ hτs hτi
  have hI : fixed τ (iwahori k (Fin d)) ≠ ⊥ := by
    refine (Submodule.ne_bot_iff _).2 ⟨v, fun h => ?_, hv0⟩
    have hg := hv h.1 (iwahori_le_KO k _ h.2)
    rw [MonoidHom.one_apply, Units.val_one, one_smul]
    show (detChar (Fin d) η⁻¹ h.1 : ℂ) • σ h.1 v = v
    rw [hg, smul_smul, detChar_apply, MonoidHom.inv_apply, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, one_smul]
  obtain ⟨α, hα⟩ := GlobalTheory.SatakeExists.exists_isSubquotient_prinSeries hadm hτi hI
  let χ : Fin d → kˣ →* ℂˣ := fun i => unrChar k (α i)
  have h1 := hα.trans (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k d χ)
  have h2 := isSubquotient_twist h1 (detChar (Fin d) η)
  rw [hτ, twist_twist_inv] at h2
  have hχs : ∀ i, IsSmoothChar (χ i) := fun i => isSmoothChar_of_isUnram (isUnram_unrChar (k := k) (α i))
  let φ := multiProdTwistEquiv (Equiv.sigmaUnique (Fin d) fun _ => Fin 1)
    (fun i => detRep (Fin 1) (χ i)) hη
  have h3 := h2.trans (.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective)
  have hfam : (fun i => twist (detRep (Fin 1) (χ i)) (detChar (Fin 1) η)) =
      fun i => detRep (Fin 1) (η * χ i) := funext fun i => twist_detRep_one _ _
  rw [hfam] at h3
  refine ⟨fun j => η * χ j, fun j => ⟨hη.mul (hχs j), fun u hu => ?_⟩, hi,
    fun j => ⟨one_pos, isIrreducible_ofChar _, isCuspidal_detRep_one (hη.mul (hχs j))⟩, _, h3⟩
  show η u * unrChar k (α j) u = η u
  rw [isUnram_unrChar (k := k) (α j) u hu, mul_one]
end UpperTheory.TNZ
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TypesNZeroPJacFin
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix
namespace UpperTheory.TNZ
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
namespace Grp
namespace JacquetFiniteLength₂
variable {n : ℕ} (G : Grp k n)
end JacquetFiniteLength₂
theorem step_jacFin_alt {n : ℕ} (G : Grp k n) : G.Step_jacFin_alt := by
  intro L V _ _ π hπ hirr
  exact ⟨isSmooth_jacU G.e hπ,
    JacquetFiniteLength₂.hasFiniteLength_jacU G L.loc.bz π hπ (hasFiniteLength_of_isIrreducible hirr)⟩
end Grp
end UpperTheory.TNZ
end
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WoConj
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open _root_.GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.GalN.V
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w} {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin n) (Qbar l)} {y : WD h}
theorem woConj'_alt (k : _root_.UpperTheory.V.Z.Win.WDT ι r y) (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {r' : G E Ω →* GL (Fin n) (Qbar l)}
    (P : GL (Fin n) (Qbar l)) (hP : ∀ g : ↥(Weil h), P * r g = r' g * P) : _root_.UpperTheory.V.Z.Win.WDT ι r' y := k.of_conj hl P hP
end UpperTheory.GalN.V
end
end
end

