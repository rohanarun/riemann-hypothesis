module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0081
public import Formalism.GL3MeanSquares.HookFormulaTorsion.DoubleCosetDecompositionAll
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0068
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0083
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.JetOpIdentityOfEntire
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.JetIdentity

open MvPolynomial

section Lin

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

omit [Fintype ι] in
theorem jetLin_add (J J' : (DVar ι a b →₀ ℕ) → K) : jetLin (J + J') = jetLin J + jetLin J' := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.add_apply, Module.Basis.constr_basis, Pi.add_apply, map_add (f := _)]

omit [Fintype ι] in
theorem jetLin_smul (c : K) (J : (DVar ι a b →₀ ℕ) → K) : jetLin (c • J) = c • jetLin J := by
  refine (basisMonomials ((ι × Fin b × Fin b) ⊕ DVar ι a b) K).ext fun m => ?_
  simp only [jetLin, LinearMap.smul_apply, Module.Basis.constr_basis, Pi.smul_apply, smul_monomial]

def jetOpL (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) :
    ((DVar ι a b →₀ ℕ) → K) →ₗ[K] (Formalism.L2.DIV.VV K lam →ₗ[K] Formalism.L2.DIV.VV K lam') where
  toFun J := jetOp lam lam' J n
  map_add' J J' := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_add, LinearMap.comp_apply, LinearMap.add_apply, map_add (f := _)]
  map_smul' c J := by
    ext1 F
    simp only [jetOp, jetMap, jetLin_smul, LinearMap.comp_apply, LinearMap.smul_apply, map_smul, RingHom.id_apply]

theorem jetOp_sum (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) {I : Type} [Fintype I] (ξ : I → K)
    (J : I → (DVar ι a b →₀ ℕ) → K) :
    ∑ i, ξ i • jetOp lam lam' (J i) n = jetOp lam lam' (∑ i, ξ i • J i) n := by
  have := map_sum (jetOpL (K := K) lam lam' n) (fun i => ξ i • J i) Finset.univ
  simp only [map_smul] at this
  exact this.symm

omit [Fintype ι] in
theorem jetLin_congr (J J' : (DVar ι a b →₀ ℕ) → K) (Q : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K)
    (h : ∀ μ ∈ Q.support, J (μ.comapDomain Sum.inr Sum.inr_injective.injOn) =
      J' (μ.comapDomain Sum.inr Sum.inr_injective.injOn)) : jetLin J Q = jetLin J' Q := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Q.as_sum, map_sum, map_sum]
  refine Finset.sum_congr rfl fun μ hμ => ?_
  have e : (monomial μ (AddMonoidAlgebra.coeff Q μ) : MvPolynomial ((ι × Fin b × Fin b) ⊕ DVar ι a b) K) =
      AddMonoidAlgebra.coeff Q μ • basisMonomials _ K μ := by
    simp [coe_basisMonomials, smul_monomial]
  rw [e, map_smul, map_smul]
  simp only [jetLin, Module.Basis.constr_basis, h μ hμ]

theorem jetOp_congr (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m : DVar ι a b →₀ ℕ, (∀ τ, ((∑ β : Fin b, ∑ α : Fin a, m (τ, β, α) : ℕ) : ℤ) =
      ∑ s : Fin a, ((lam τ).w s - (lam τ).detShift + (n τ : ℤ))) → J m = J' m) :
    jetOp lam lam' J n = jetOp lam lam' J' n := by
  classical
  ext1 F
  simp only [jetOp, jetMap, LinearMap.comp_apply]
  congr 1
  refine jetLin_congr J J' _ fun μ hμ => h _ fun τ => ?_
  have h1 := GlobalTheory.JetDeg.subD_hom (b := b) τ (GlobalTheory.JetDeg.sharp_hom n τ (GlobalTheory.JetDeg.VV_hom lam τ F.2)) (mem_support_iff.mp hμ)
  rw [GlobalTheory.JetDeg.weight_derW] at h1
  simp only [Finsupp.comapDomain_apply]
  rw [h1]
  push_cast
  simp [GlobalTheory.JetDeg.natW_cast, Finset.sum_add_distrib, mul_comm]

end Lin

section An

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetC_sum (cD : ι → ℂ) {I : Type} [Fintype I] (c : I → ℂ) (G : I → VCx ι a b → ℂ)
    (hG : ∀ i, AnalyticOnNhd ℂ (G i) Set.univ) (m : DVar ι a b →₀ ℕ) :
    jetC cD (fun z => ∑ i, c i * G i z) m = ∑ i, c i * jetC cD (G i) m := by
  have hc : ∀ i (k : ℕ), ContDiff ℂ k (G i) := fun i k => (hG i).contDiff
  have e : (fun z => ∑ i, c i * G i z) = fun z => ∑ i, (c i • G i) z := by
    funext z; simp
  unfold jetC derivAt0
  rw [e, iteratedFDeriv_sum (f := fun i => c i • G i) (fun i _ => (hc i _).const_smul (c i))]
  simp only [Finset.sum_apply, ContinuousMultilinearMap.sum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_const_smul_apply (hc i _).contDiffAt]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring

theorem map_desc {K : Type} [Field K] (σ : K →+* ℂ) {z : ℂ} (h : ∃ k : K, σ k = z) : σ (desc σ z) = z := by
  rw [desc, dite_eq_left h]
  exact h.choose_spec

end An

end GlobalTheory.JetIdentity


open GlobalTheory.JetIdentity in
theorem GlobalTheory.jetOp_identity_of_entire : ∀ (X : Fields) (a b : ℕ) (σ : X.K →+* ℂ) (cD : X.Tau → ℂ) (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ) (I₁ I₂ : Type) [Fintype I₁] [Fintype I₂] (ξ₁ : I₁ → X.K) (ξ₂ : I₂ → X.K) (G₁ : I₁ → VCx X.Tau a b → ℂ) (G₂ : I₂ → VCx X.Tau a b → ℂ) (u₁ u₂ : ℂ) (r : X.K), (∀ i, AnalyticOnNhd ℂ (G₁ i) Set.univ) → (∀ i, AnalyticOnNhd ℂ (G₂ i) Set.univ) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₁ * jetC cD (G₁ i) m) → (∀ i (m : DVar X.Tau a b →₀ ℕ), (∀ τ, (degAt m τ : ℤ) = degNu lam n τ) → ∃ k : X.K, σ k = u₂ * jetC cD (G₂ i) m) → (∀ z, ∑ i, σ (ξ₁ i) * (u₁ * G₁ i z) = σ r * ∑ i, σ (ξ₂ i) * (u₂ * G₂ i z)) → ∑ i, ξ₁ i • jetOp lam lam' (fun m => desc σ (u₁ * jetC cD (G₁ i) m)) n = r • ∑ i, ξ₂ i • jetOp lam lam' (fun m => desc σ (u₂ * jetC cD (G₂ i) m)) n := by
  intro X a b σ cD lam lam' n I₁ I₂ _ _ ξ₁ ξ₂ G₁ G₂ u₁ u₂ r hG₁ hG₂ hr₁ hr₂ hz
  rw [jetOp_sum, jetOp_sum]
  refine Eq.trans ?_ ((jetOpL lam lam' n).map_smul r _)
  refine jetOp_congr lam lam' n _ _ fun m hm => ?_
  apply σ.injective
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_mul, map_sum]
  have h1 := jetC_sum cD (fun i => σ (ξ₁ i) * u₁) G₁ hG₁ m
  have h2 := jetC_sum cD (fun i => σ r * (σ (ξ₂ i) * u₂)) G₂ hG₂ m
  have e : (fun z => ∑ i, σ (ξ₁ i) * u₁ * G₁ i z) = fun z => ∑ i, σ r * (σ (ξ₂ i) * u₂) * G₂ i z := by
    funext z
    have := hz z
    rw [Finset.mul_sum] at this
    simpa only [mul_assoc] using this
  rw [e, h2] at h1
  rw [Finset.mul_sum]
  simp only [fun i => map_desc σ (hr₁ i m hm), fun i => map_desc σ (hr₂ i m hm)]
  simpa only [mul_assoc] using h1.symm

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainUOperatorCommutationOfPointPairLaw
section
open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

noncomputable section

namespace GlobalTheory.LvT

theorem count_incidence {G P C V : Type} [Group G] [MulAction G P] [Fintype C] [AddCommGroup V] [Module ℂ V]
    (rep : C → P) (hsurj : ∀ p, ∃ (c : C) (g : G), g • rep c = p)
    (hinj : ∀ (c c' : C) (g : G), g • rep c = rep c' → c = c')
    (hfin : ∀ c, Finite (MulAction.stabilizer G (rep c)))
    (I : P → P → Prop) (hup : ∀ p, {q | I p q}.Finite) (hdn : ∀ p, {q | I q p}.Finite)
    (hI : ∀ (g : G) p q, I p q → I (g • p) (g • q))
    (F : P → P → V) (hF : ∀ (g : G) p q, F (g • p) (g • q) = F p q) :
    ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ q ∈ {q | I (rep c) q}, F (rep c) q =
      ∑ c, ((Nat.card (MulAction.stabilizer G (rep c)) : ℂ))⁻¹ • ∑ᶠ p ∈ {p | I p (rep c)}, F p (rep c) := by
  letI : Module ℚ V := Module.compHom V (algebraMap ℚ ℂ)
  have hfin' : ∀ p : P, Finite (MulAction.stabilizer G p) := by
    intro p
    obtain ⟨c, g, rfl⟩ := hsurj p
    haveI := hfin c
    exact Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (a := rep c) (g := g) rfl).toEquiv
  have hR : ∀ a : P, ∃! r, r ∈ Finset.univ.image rep ∧ r ∈ MulAction.orbit G a := by
    intro a
    obtain ⟨c, g, rfl⟩ := hsurj a
    refine ⟨rep c, ⟨Finset.mem_image_of_mem _ (Finset.mem_univ _), g⁻¹, inv_smul_smul g _⟩, ?_⟩
    rintro r ⟨hr, γ, hγ⟩
    obtain ⟨c', -, rfl⟩ := Finset.mem_image.mp hr
    have : c = c' := hinj c c' (γ * g) (by rw [mul_smul]; exact hγ)
    rw [this]
  have hrinj : Function.Injective rep := fun c c' h => hinj c c' 1 (by rw [one_smul, h])
  have key := Formalism.HermitianLattices.RamifiedLatticeOperators.count_of_orbits G P P V (fun a => (hup a).toFinset) (fun b => (hdn b).toFinset) F
    (Finset.univ.image rep) (Finset.univ.image rep) (by intro a b; simp)
    (by intro γ a b h; simp only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] at h ⊢; exact hI γ a b h)
    (fun γ a b _ => hF γ a b) hfin' hfin' hR hR
  rw [Finset.sum_image (fun a _ b _ h => hrinj h), Finset.sum_image (fun a _ b _ h => hrinj h)] at key
  have hq : ∀ (n : ℕ) (x : V), ((n : ℚ))⁻¹ • x = ((n : ℂ))⁻¹ • x := by
    intro n x
    change (algebraMap ℚ ℂ ((n : ℚ))⁻¹) • x = _
    simp
  simp only [hq] at key
  simp only [finsum_mem_eq_finite_toFinset_sum _ (hup _), finsum_mem_eq_finite_toFinset_sum _ (hdn _)]
  exact key

theorem levelChainUOperatorCommutation_of_pointPairLaw : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (Lv : LevTie X) (Kt : KerTie Lv),
    (∀ i h, (Kt i h).TgtEq) → (∀ i h, (Kt i h).UKLaw) → LevelChainUOperatorCommutation X := by
  intro D u X Lv Kt htgt huk i hi v φ hφ
  set M := Lv i hi.le with hM
  set M' := Lv (i + 1) hi with hM'
  let K : KerPt M M' := Kt i hi
  have hT : K.TgtEq := htgt i hi
  have hU : K.UKLaw := huk i hi
  obtain ⟨Φ, hΦ⟩ := (_root_.GlobalTheory.LvT.PtModel.mem_Fi_iff_exists_isExt D u X i M φ).1 hφ
  obtain ⟨hfinI, hstab, -⟩ := _root_.GlobalTheory.LvT.inc_finite_stable D u X i M v
  obtain ⟨hfinI', -, -⟩ := _root_.GlobalTheory.LvT.inc_finite_stable D u X (i + 1) M' v
  have h1 := _root_.GlobalTheory.LvT.uop_isExt D u X (i + 1) M' v _ _ (_root_.GlobalTheory.LvT.isExt_KT D u X i M M' K φ Φ hT hΦ)
  have h2 := _root_.GlobalTheory.LvT.isExt_KT D u X i M M' K _ _ hT (_root_.GlobalTheory.LvT.uop_isExt D u X i M v φ Φ hΦ)
  have hpow : ((((X.A.T : ℝ) ^ (((D.R.t : ℝ) + 1) / 2) : ℝ)) : ℂ) = (X.A.T : ℂ) ^ ((D.R.t + 1) / 2) := by
    obtain ⟨k, hk⟩ := D.R.t_odd
    have e1 : (D.R.t + 1) / 2 = k + 1 := by omega
    have e2 : ((D.R.t : ℝ) + 1) / 2 = ((k + 1 : ℕ) : ℝ) := by rw [hk]; push_cast; ring
    rw [e1, e2, Real.rpow_natCast]
    push_cast; rfl
  have hwt : ∀ c, X.C.wt i c = ((Nat.card (MulAction.stabilizer M.G (M.rep c)) : ℂ))⁻¹ := by
    intro c
    rw [← M.card_stab]; rfl
  have hfs : ∀ c, Finite (MulAction.stabilizer M.G (M.rep c)) := by
    intro c
    apply Nat.finite_of_card_ne_zero
    rw [← M.card_stab]
    haveI := X.C.stabFin i c
    letI := X.C.stabGrp i c
    exact Nat.card_pos.ne'
  funext c'
  rw [hpow, Pi.smul_apply, h1.1 c', h2.1 c', ← Submodule.coe_smul]
  congr 1
  have key := count_incidence M.rep M.rep_surj M.rep_inj hfs (M.Inc v) (fun p => (hfinI p).1) (fun p => (hfinI p).2)
    (fun g p q h => (hstab g p q).1 h) (fun p q => K.k p (M'.rep c') (Φ q))
    (fun g p q => by rw [hΦ.2, K.src])
  have hL : ∀ c, K.k (M.rep c) (M'.rep c') (∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, Φ p₁) =
      ∑ᶠ p₁ ∈ {p₁ | M.Inc v (M.rep c) p₁}, K.k (M.rep c) (M'.rep c') (Φ p₁) := by
    intro c
    set_option synthInstance.maxHeartbeats 100000 in
      rw [finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, finsum_mem_eq_finite_toFinset_sum _ (hfinI _).1, map_sum]
  simp only [hL, hwt]
  rw [key, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1, Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [← Finset.smul_sum, smul_comm, ← hU v, finsum_mem_eq_finite_toFinset_sum _ (hfinI' _).1]

end GlobalTheory.LvT
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingNonvanishingIffEventuallyNonzero
section
open NumberField IsDedekindDomain

noncomputable section

namespace GlobalTheory.QNormal

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV _root_.Formalism.L2.Col

section General

variable {E : Type} [Field E] [NumberField E] {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem IntHom.comp {a b c : ℕ} {x : (Fin b → E) →ₗ[E] (Fin c → E)} {y : (Fin a → E) →ₗ[E] (Fin b → E)}
    (hx : IntHom P x) (hy : IntHom P y) : IntHom P (x ∘ₗ y) := fun v hv => hx _ (hy v hv)

theorem IntHom.pow_mono {a b : ℕ} {x : (Fin a → E) →ₗ[E] (Fin b → E)} {N N' : ℕ} (h : N ≤ N')
    (hx : IntHom P (((qOf P : E) ^ N) • x)) : IntHom P (((qOf P : E) ^ N') • x) :=
  fun v hv l => Proof.NormalFormAtPrime.intAt_pow_mono h (hx v hv l)

theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N i : ℕ) : IntV P (Loc.eN E N i) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem intAt_chArg {n' c' n c : ℕ} {x : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E)} {u : E} (hx : IntHom P (u • x)) :
    IntAt P (u * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with h
  · exact hx _ (intV_eN P _ _) _
  · simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem unfNe_transfer [CharZero K] (hP : IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P) {n' c' n c : ℕ} (hc : 1 ≤ c) (hc' : c' = c + 1)
    {psi : E → K} {D N : ℕ} (hN : N ≤ D) (hpsi : CharTo P D psi) {Psi Psi' : Loc.SF E K (n' + c') (n + c)}
    (h1 : HomBdd P N Psi) (h2 : HomBdd P N Psi') {C : K} (hC : C ≠ 0)
    {r : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E)} {r' : (Fin (n' + c') → E) ≃ₗ[E] (Fin (n' + c') → E)}
    (hr : r ∈ Loc.R1 E n c) (hr' : r' ∈ Loc.R1 E n' c')
    (hrel : ∀ x, Psi' x = C * Psi (r.toLinearMap ∘ₗ x ∘ₗ r'.toLinearMap)) (H : UnfNe P psi Psi) : UnfNe P psi Psi' := by
  obtain ⟨A₀, B₀, H⟩ := H
  obtain ⟨xj', hx⟩ := Function.ne_iff.1 (H (max A₀ N) (max B₀ N) (le_max_left _ _) (le_max_left _ _))
  obtain ⟨xj, T, b, hT⟩ := _root_.GlobalTheory.Proof.unipotentRadicals_act_affine_unfoldingSpaces.affine_action _root_.GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic E n' c' n c hc hc' r hr r' hr' xj'
  obtain ⟨d, hd⟩ := _root_.GlobalTheory.Proof.unfoldingCharacterArgument_comp_unipotentRadicals.chArg_comp _root_.GlobalTheory.Proof.exists_xx1_eq_iff_inX_eN_Ufl_conditions.unfoldingAffineSpace_mem_iff_intrinsic E n' c' n c hc hc' r hr r' hr'
  have I1 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi hN hpsi h1 xj'
  have I2 := GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz E K P n' c' n c psi D N Psi' hN hpsi h2 xj
  obtain ⟨A₁, B₁, hA⟩ := GlobalTheory.T.boxSum_ne_zero_invariant_affineChange _root_.GlobalTheory.Proof.vectors_linearMaps_bounded_denominators_atPrime.bounded_denominators _root_.GlobalTheory.Proof.sum_coset_reps_ne_zero_iff_commensurable.sum_reps_ne_zero_iff _root_.GlobalTheory.Proof.rationalFractions_represent_primeNormQuotient.valsQ_reps E K P hP _ (integrand psi Psi xj') N I1.1 T b
  refine ⟨max A₁ N, max B₁ N, fun A B hA' hB' => Function.ne_iff.2 ⟨xj, ?_⟩⟩
  have h3 : boxSum P A B (integrand psi Psi xj') ≠ 0 := by
    rw [_root_.GlobalTheory.boxSum_eq_of_funBdd E K P hP.1 _ _ N I1.1 A B (le_of_max_le_right hA') (le_of_max_le_right hB'),
      ← _root_.GlobalTheory.boxSum_eq_of_funBdd E K P hP.1 _ _ N I1.1 (max A₀ N) (max B₀ N) (le_max_right _ _) (le_max_right _ _)]
    exact hx
  have h4 := (hA A B (le_of_max_le_left hA') (le_of_max_le_left hB')).2 h3
  have hdep : ∀ t, Psi (Loc.xx1 xj' (T t + b)) ≠ 0 → IntAt P ((qOf P : E) ^ D * d) ∧
      IntAt P ((qOf P : E) ^ D * -Loc.chArg (Loc.xx1 xj' (T t + b))) := by
    intro t ht
    have a1 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I1.2 _ ht)
    have a2 := Proof.NormalFormAtPrime.intAt_pow_mono hN (I2.2 t (by rw [hrel, hT]; exact mul_ne_zero hC ht))
    refine ⟨?_, by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a1⟩
    have := a1.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a2)
    rw [← hT, hd] at this
    convert this using 1
    ring
  have hpt : ∀ t, integrand psi Psi' xj t = C * psi d * integrand psi Psi xj' (T t + b) := by
    intro t
    unfold integrand
    rw [hrel, hT]
    by_cases ht : Psi (Loc.xx1 xj' (T t + b)) = 0
    · simp [ht]
    · have e : -Loc.chArg (Loc.xx1 xj t) = d + -Loc.chArg (Loc.xx1 xj' (T t + b)) := by
        rw [← hT, hd]
        ring
      rw [e, hpsi.1 _ _ (hdep t ht).1 (hdep t ht).2]
      ring
  have hd0 : psi d ≠ 0 := by
    obtain ⟨t, -, ht⟩ := Finset.exists_ne_zero_of_sum_ne_zero (right_ne_zero_of_mul h4)
    have a := (hdep t (left_ne_zero_of_mul ht)).1
    have := hpsi.1 d (-d) a (by simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg a)
    rw [add_neg_cancel, hpsi.2 0 (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P)] at this
    exact left_ne_zero_of_mul (this ▸ one_ne_zero)
  change boxSum P A B (integrand psi Psi' xj) ≠ 0
  have e : boxSum P A B (integrand psi Psi' xj) =
      C * psi d * boxSum P A B (fun t => integrand psi Psi xj' (T t + b)) := by
    unfold boxSum
    simp only [hpt, ← Finset.mul_sum]
    ring
  rw [e]
  exact mul_ne_zero (mul_ne_zero hC hd0) h4

theorem homBdd_translate {a b i : ℕ} {Φ Psi : Loc.SF E K a b} {C : K} {g : (Fin a → E) ≃ₗ[E] (Fin a → E)}
    {h : (Fin b → E) ≃ₗ[E] (Fin b → E)} (hΦ : ∀ x, Φ x ≠ 0 → IntHom P x)
    (hΦ' : ∀ x y, IntHom P y → Φ (x + (qOf P : E) • y) = Φ x)
    (g1 : IntHom P g.symm.toLinearMap) (g2 : IntHom P (((qOf P : E) ^ i) • g.toLinearMap))
    (h1 : IntHom P h.symm.toLinearMap) (h2 : IntHom P (((qOf P : E) ^ (i + 1)) • h.toLinearMap))
    (e : ∀ x, Psi x = C * Φ (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap)) : HomBdd P (i + 1) Psi := by
  refine ⟨fun x hx v hv => ?_, fun x y hy => ?_⟩
  · rw [e] at hx
    have := h2 _ (hΦ _ (right_ne_zero_of_mul hx) _ (g1 v hv))
    simpa using this
  · rw [e, e, ← hΦ' (h.symm.toLinearMap ∘ₗ x ∘ₗ g.toLinearMap) _ (h1.comp (hy.comp g2))]
    congr 2
    refine LinearMap.ext fun v => ?_
    simp [pow_succ', mul_smul]

end General

section Chain

open IndefiniteRowSideFullHecke.SandwichNormalForm

variable {X : Fields} {Pr : Primes X} {R : Ranks}

def Between (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) : Prop :=
  IntHom P h.symm.toLinearMap ∧ IntHom P (((qOf P : X.E) ^ j) • h.toLinearMap)

theorem between_iff {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) (h : AutY X R j) :
    (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, h⁻¹ x ∈ lamYat (Pr := Pr) (R := R) j P ∧
      ((qOf P : X.E) ^ j) • h x ∈ lamYat (Pr := Pr) (R := R) j P) ↔ Between j P h := by
  simp only [mem_lamYat hP]
  exact ⟨fun H => ⟨fun v hv => (H v hv).1, fun v hv => (H v hv).2⟩, fun H v hv => ⟨H.1 v hv, H.2 v hv⟩⟩

theorem between_of_nf {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) {h : AutY X R j} (H : NF Pr j P h) :
    Between j P h := by
  obtain ⟨h1, h2⟩ := _root_.GlobalTheory.Proof.latticeSandwich_of_latticeNormalForm.inclAt X Pr R j P hP h 1 H (one_mem _)
  rw [mul_one] at h1 h2
  refine (between_iff hP h).1 fun x hx => ⟨?_, h2 x hx⟩
  obtain ⟨y, hy, rfl⟩ := h1 x hx
  rwa [show h⁻¹ (h y) = y from h.symm_apply_apply y]

theorem sameDC_symm {sharp : Bool} {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} {h h' : AutY X R j}
    (a : SameDC (Pr := Pr) sharp j P h h') : SameDC (Pr := Pr) sharp j P h' h := by
  obtain ⟨r, hr, k, hk, rfl⟩ := a
  exact ⟨r⁻¹, inv_mem hr, k⁻¹, inv_mem hk, by group⟩

theorem sameDC_mul (sharp : Bool) {j : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (h : AutY X R j) {r : AutY X R j}
    (hr : r ∈ Loc.R1 X.E (R.N j) (cOf R j)) : SameDC (Pr := Pr) sharp j P h (r * h) :=
  ⟨r, hr, 1, one_mem _, (mul_one _).symm⟩

variable (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))

def omScal (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu cst i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu cst i P (LinearEquiv.det h : X.Eˣ))⁻¹ *
    cst.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * (R.N (i + 1) + cOf R (i + 1) : ℕ)) *
    cst.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det h : X.Eˣ) * (R.N i + cOf R i : ℕ))

theorem omPhi_eq (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P hal h x =
      omScal Ch sel mu cst i P hal h * PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) := rfl

theorem localUnfoldingNonvanishing_iff_eventuallyNonzero (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (h : AutY X R (i + 1)) :
    FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h ↔ UnfNe P.1 (cst.psi P) (omPhi Ch sel mu cst i P hal h) := Iff.rfl

variable {Ch sel mu cst}

theorem omScal_ne_zero (hc : cst.Ok) {i : ℕ} {P : rowSG Pr sel mu} (hd : DegOne P.1) (hm : cst.muq (i + 1) P ≠ 0)
    (hal : AutY X R i) (h : AutY X R (i + 1)) : omScal Ch sel mu cst i P hal h ≠ 0 := by
  have hq : cst.sq P ≠ 0 := by
    intro e
    have := hc.sq_sq P
    rw [e, zero_pow two_ne_zero] at this
    exact hd.1.ne_zero (by exact_mod_cast this.symm)
  have hmu : ∀ a : X.Eˣ, muAt Ch sel mu cst i P a ≠ 0 := fun a => _root_.GlobalTheory.Proof.localCharacter_ne_zero_of_ne_zero.locChar_ne_zero X.E X.K P.1 hd _ _ _ hm a.ne_zero
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (hmu _) (inv_ne_zero (hmu _))) (zpow_ne_zero _ hq)) (zpow_ne_zero _ hq)

theorem rank_le (R : Ranks) (j : ℕ) : R.k ≤ R.N j ∧ R.r ≤ R.N j + cOf R j := by
  have : j ≤ j * (R.t + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  unfold Ranks.N Ranks.r cOf
  omega

theorem phiAt_prop {sharp : Bool} {i : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (∀ x, PhiAt Ch mu sharp i P x ≠ 0 → IntHom P x) ∧
      ∀ x y, IntHom P y → PhiAt Ch mu sharp i P (x + (qOf P : X.E) • y) = PhiAt Ch mu sharp i P x := by
  unfold PhiAt
  rw [if_neg hP]
  exact _root_.GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant.phiQ_bdd X.E X.K P _ _ _ _ _ _ _ (rank_le R i).1 (rank_le R (i + 1)).1 (rank_le R i).2 (rank_le R (i + 1)).2

theorem omPhi_bdd {i : ℕ} {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h1 : Between i P.1 hal) (h2 : Between (i + 1) P.1 h) : HomBdd P.1 (i + 1) (omPhi Ch sel mu cst i P hal h) :=
  homBdd_translate (phiAt_prop hP).1 (phiAt_prop hP).2 h1.1 h1.2 h2.1 h2.2 (omPhi_eq Ch sel mu cst i P hal h)

theorem omPhi_mul {i : ℕ} {P : rowSG Pr sel mu} {hal : AutY X R i} {h : AutY X R (i + 1)}
    (h0 : omScal Ch sel mu cst i P hal h ≠ 0) (ρ' : AutY X R i) (ρ : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P (ρ' * hal) (ρ * h) x =
      omScal Ch sel mu cst i P (ρ' * hal) (ρ * h) / omScal Ch sel mu cst i P hal h *
        omPhi Ch sel mu cst i P hal h ((ρ⁻¹).toLinearMap ∘ₗ x ∘ₗ ρ'.toLinearMap) := by
  rw [omPhi_eq, omPhi_eq, ← mul_assoc, div_mul_cancel₀ _ h0]
  rfl

theorem first_unipotent_class_transfer (hc : cst.Ok) {i : ℕ} (hi : i + 1 ≤ R.m - 2) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hd : DegOne P.1)
    (hm : cst.muq (i + 1) P ≠ 0) (hD : i + 1 ≤ cst.D P) {hal hal' ρ' : AutY X R i} {h h' ρ : AutY X R (i + 1)}
    (hρ' : ρ' ∈ Loc.R1 X.E _ _) (hρ : ρ ∈ Loc.R1 X.E _ _) (e' : hal' = ρ' * hal) (e : h' = ρ * h)
    (a1 : Between i P.1 hal) (a2 : Between i P.1 hal') (b1 : Between (i + 1) P.1 h) (b2 : Between (i + 1) P.1 h')
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal' h' := by
  rw [localUnfoldingNonvanishing_iff_eventuallyNonzero] at H ⊢
  subst e e'
  exact unfNe_transfer hd (by unfold cOf; omega) (by unfold cOf; omega) hD ⟨hc.psi_add P, hc.psi_int P⟩
    (omPhi_bdd hP a1 b1) (omPhi_bdd hP a2 b2)
    (div_ne_zero (omScal_ne_zero hc hd hm _ _) (omScal_ne_zero hc hd hm _ _)) (inv_mem hρ) hρ'
    (omPhi_mul (omScal_ne_zero hc hd hm _ _) ρ' ρ) H

theorem lamYat_coe {j : ℕ} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    (lamYat (Pr := Pr) (R := R) j P : Set (Sp X.E (R.N j + cOf R j))) = {v | IntV P v} :=
  Set.ext fun v => mem_lamYat hP v

variable {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

end Chain

end GlobalTheory.QNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowLStarStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sizes_b_add_Sc_add_etaSz_add_div_lt_lStar : SzRow (fun C D L => (L.sc.b' + L.Sc + L.etaSz + L.sc.b / lStar L < lStar L) ∧ (2 * L.etaSz + D.R.t + 8 * L.sc.b / lStar L + 7 < lStar L)) := by
  first | exact @GlobalTheory.EX.szRow_lStar | exact GlobalTheory.EX.szRow_lStar | (intros; apply GlobalTheory.EX.szRow_lStar <;> assumption)
end

