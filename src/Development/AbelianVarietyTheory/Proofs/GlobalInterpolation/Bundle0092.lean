module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StatementWithTransposeOfBranching
public import Formalism.LocalToGlobal.Columns.PolyFnLemmas
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WindowsOfExplicitParameters
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InterTransport
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.Transport

variable {V V' : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']

theorem opU_comp (e : V ≃ₗ[ℂ] V') {H : Sesq V} {H' : Sesq V'} (hH : ∀ x y, H' (e x) (e y) = H x y)
    (F : V' → ℂ) (x z : V) : opU H x (fun w => F (e w)) z = opU H' (e x) F (e z) := by
  simp only [opU, hH, map_add (f := _)]

def subEquiv (e : V ≃ₗ[ℂ] V') {Λ : AddSubgroup V} {Λ' : AddSubgroup V'} (h : ∀ x, x ∈ Λ ↔ e x ∈ Λ') : Λ ≃+ Λ' where
  toFun x := ⟨e x, (h _).1 x.2⟩
  invFun y := ⟨e.symm y, (h _).2 (by simp)⟩
  left_inv x := by simp
  right_inv y := by simp
  map_add' x y := by simp

def quotEquiv (e : V ≃ₗ[ℂ] V') {Λ₁ Λ₂ : AddSubgroup V} {Λ₁' Λ₂' : AddSubgroup V'} (h₁ : ∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁')
    (h₂ : ∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') : (Λ₂ ⧸ Λ₁.addSubgroupOf Λ₂) ≃+ (Λ₂' ⧸ Λ₁'.addSubgroupOf Λ₂') :=
  QuotientAddGroup.congr _ _ (subEquiv e h₂) (by
    ext y
    obtain ⟨x, rfl⟩ := (subEquiv e h₂).surjective y
    exact (AddSubgroup.mem_map_iff_mem (f := (subEquiv e h₂ : Λ₂ →+ Λ₂')) (subEquiv e h₂).injective).trans (h₁ _))

theorem term_add {H : Sesq V} {α : V → ℂ} (hH : IsHerm H) {A₁ A₂ : AddSubgroup V} (hd : IsSelfDual H A₂)
    (hs : IsSemiChar H A₂ α) {F : V → ℂ} (hF : F ∈ fixedBy H α A₁) {a s : V} (ha : a ∈ A₂) (hs₂ : s ∈ A₂)
    (hs₁ : s ∈ A₁) (z : V) : α (a + s) * opU H (a + s) F z = α a * opU H a F z := by
  rw [GlobalTheory.ThetaInter.alpha_opU_add hH hd hs ha hs₂, ← GlobalTheory.ThetaInter.opU_mul]
  congr 2
  funext w
  exact hF s hs₁ w

theorem inter_transport : ∀ (V V' : Type) [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] (e : V ≃ₗ[ℂ] V') (H : Sesq V) (H' : Sesq V') (α : V → ℂ) (α' : V' → ℂ) (Λ₁ Λ₂ : AddSubgroup V) (Λ₁' Λ₂' : AddSubgroup V') (θ' : V' → ℂ), (∀ x y, H' (e x) (e y) = H x y) → (∀ x, x ∈ Λ₁ ↔ e x ∈ Λ₁') → (∀ x, x ∈ Λ₂ ↔ e x ∈ Λ₂') → (∀ x ∈ Λ₂, α x = α' (e x)) → IsHerm H' → IsSelfDual H' Λ₂' → IsSemiChar H' Λ₂' α' → (IsSelfDual H Λ₂ ∧ IsSemiChar H Λ₂ α ∧ ∀ F' ∈ fixedBy H' α' Λ₂', (fun z => F' (e z)) ∈ fixedBy H α Λ₂) ∧ (θ' ∈ fixedBy H' α' Λ₁' → relIdx Λ₁' Λ₂' ≠ 0 → inter H α Λ₁ Λ₂ (fun z => θ' (e z)) = fun z => inter H' α' Λ₁' Λ₂' θ' (e z)) := by
  intro V V' _ _ _ _ e H H' α α' Λ₁ Λ₂ Λ₁' Λ₂' θ' hH h₁ h₂ hα hh hd hs
  have hE : ∀ x y, altE H x y = altE H' (e x) (e y) := fun x y => by simp only [altE, hH]
  refine ⟨⟨?_, ⟨fun x hx => ?_, fun x hx y hy => ?_⟩, fun F hF x hx z => ?_⟩, fun hθ _ => ?_⟩
  · ext x
    rw [h₂ x]
    conv_rhs => rw [← hd]
    constructor
    · intro h y hy
      obtain ⟨y, rfl⟩ := e.surjective y
      rw [← hE]
      exact h y ((h₂ y).2 hy)
    · intro h y hy
      rw [hE]
      exact h _ ((h₂ y).1 hy)
  · rw [hα x hx]; exact hs.1 _ ((h₂ x).1 hx)
  · rw [hα _ (Λ₂.add_mem hx hy), hα x hx, hα y hy, map_add (f := _), hE]
    exact hs.2 _ ((h₂ x).1 hx) _ ((h₂ y).1 hy)
  · rw [opU_comp e hH, hα x hx]
    exact hF _ ((h₂ x).1 hx) _
  · funext z
    have hc : relIdx Λ₁ Λ₂ = relIdx Λ₁' Λ₂' := Nat.card_congr (quotEquiv e h₁ h₂).toEquiv
    rw [inter, inter, hc, ← finsum_comp_equiv (quotEquiv e h₁ h₂).toEquiv]
    congr 1
    refine finsum_congr fun c => ?_
    rw [opU_comp e hH, hα _ (Quotient.out c).2]
    have hm : -(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c) ∈
        Λ₁'.addSubgroupOf Λ₂' := by
      rw [← QuotientAddGroup.eq, QuotientAddGroup.out_eq']
      conv_rhs => rw [← QuotientAddGroup.out_eq' c]
      rfl
    have := term_add hh hd hs hθ (subEquiv e h₂ (Quotient.out c)).2
      (-(subEquiv e h₂ (Quotient.out c)) + Quotient.out ((quotEquiv e h₁ h₂).toEquiv c)).2
      (AddSubgroup.mem_addSubgroupOf.1 hm) (e z)
    rw [← AddSubgroup.coe_add, add_neg_cancel_left] at this
    exact this.symm

end GlobalTheory.ThetaMove.Transport
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.InvTrKEmbGLApply
section
noncomputable section

namespace GlobalTheory.LvT.BuiltChain

open NumberField IsDedekindDomain Formalism.BasicNotions _root_.Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Matrix

section General

variable {E K ι : Type} [Field E] [NumberField E] [Field K] [NumberField K] [Fintype ι] (emb : ι → E →+* K)


omit [Fintype ι] in
theorem mem_dualFr_tauLat {n : ℕ} (τ : ι) (L : Submodule (𝓞 E) (Fin n → E)) (φ : Fin n → K) :
    φ ∈ dualFr (tauLat emb τ L) ↔ ∀ y ∈ L, φ ⬝ᵥ (fun a => emb τ (y a)) ∈ (1 : Submodule (𝓞 K) K) := by
  constructor
  · intro h y hy
    exact h _ (Submodule.subset_span ⟨y, hy, rfl⟩)
  · intro h x hx
    induction hx using Submodule.span_induction with
    | mem z hz => obtain ⟨y, hy, rfl⟩ := hz; exact h y hy
    | zero => simp
    | add y z _ _ hy hz => rw [dotProduct_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [dotProduct_smul]; exact Submodule.smul_mem _ c hy


omit [Fintype ι] in
theorem dualFr_tauLat_sum {N n : ℕ} (hN : N = n + 1) (τ : ι) {t : E} (ht : t ≠ 0) (L : Submodule (𝓞 E) (Fin N → E))
    (L' : Submodule (𝓞 E) (Fin n → E))
    (hL : ∀ x, x ∈ L ↔ iniH hN x ∈ L' ∧ t * x (Br.iL hN) ∈ (1 : Submodule (𝓞 E) E)) :
    dualFr (tauLat emb τ L) = Br.sumLat hN (dualFr (tauLat emb τ L')) (emb τ t) := by
  subst hN
  ext φ
  rw [mem_dualFr_tauLat]
  change _ ↔ (fun a : Fin n => φ a.castSucc) ∈ dualFr (tauLat emb τ L') ∧ ∃ c : 𝓞 K, φ (Fin.last n) = (c : K) * emb τ t
  replace hL : ∀ x, x ∈ L ↔ (fun a : Fin n => x a.castSucc) ∈ L' ∧ t * x (Fin.last n) ∈ (1 : Submodule (𝓞 E) E) := hL
  rw [mem_dualFr_tauLat]
  have e : ∀ y : Fin (n + 1) → E, φ ⬝ᵥ (fun a => emb τ (y a)) =
      (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun a => emb τ (y a.castSucc)) + φ (Fin.last n) * emb τ (y (Fin.last n)) := by
    intro y
    simp only [dotProduct, Fin.sum_univ_castSucc]
  have ht' : emb τ t ≠ 0 := (map_ne_zero _).2 ht
  constructor
  · intro h
    refine ⟨fun y hy => ?_, ?_⟩
    · have := h (Fin.snoc y 0) ((hL _).2 ⟨by simpa using hy, by simp⟩)
      rw [e] at this
      simpa using this
    · have := h (Fin.snoc (0 : Fin n → E) t⁻¹) ((hL _).2 ⟨by simp only [Fin.snoc_castSucc]; exact L'.zero_mem, by
        rw [Fin.snoc_last, mul_inv_cancel₀ ht]; exact Submodule.mem_one.2 ⟨1, map_one _⟩⟩)
      rw [e] at this
      simp only [Fin.snoc_castSucc, Fin.snoc_last, Pi.zero_apply, map_zero] at this
      have h0 : (fun a : Fin n => φ a.castSucc) ⬝ᵥ (fun _ => (0 : K)) = 0 := dotProduct_zero _
      rw [h0, zero_add, map_inv₀] at this
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 this
      refine ⟨c, ?_⟩
      change _ = algebraMap (𝓞 K) K c * _
      rw [hc, inv_mul_cancel_right₀ ht']
  · rintro ⟨h1, c, hc⟩ y hy
    obtain ⟨h2, h3⟩ := (hL y).1 hy
    obtain ⟨r, hr⟩ := Submodule.mem_one.1 h3
    rw [e]
    refine Submodule.add_mem _ (h1 _ h2) ?_
    rw [hc, mul_assoc, ← map_mul, ← hr]
    exact Submodule.mem_one.2 ⟨c * RingOfIntegers.mapRingHom (emb τ) r, by rw [map_mul]; rfl⟩


omit [NumberField E] [NumberField K] [Fintype ι] in
theorem invTrK_embGL_apply {n : ℕ} (γ : GL (Fin n) E) (τ : ι) (a b : Fin n) :
    ((invTrK (embGL emb γ) τ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) a b =
      emb τ (((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) b a) := by
  simp only [invTrK, inside₂, embGL, Formalism.UG.bc, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.pi_apply,
    transpose_apply, ← map_inv]
  rfl


omit [NumberField E] in
theorem brAt_rhoVr {N n : ℕ} (hN : N = n + 1) {lam : ι → DomWeight N} {sg : ι → DomWeight n}
    (hI : ∀ τ, Br.Interlace hN (lam τ) (sg τ)) (hS : ∀ τ, Br.SameShift (lam τ) (sg τ)) (t : ι → K)
    (γ : GL (Fin n) E) (γ' : GL (Fin N) E)
    (h1 : ∀ x, iniH hN (((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) =
      ((γ⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ iniH hN x)
    (h2 : ∀ x, (((γ'⁻¹ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) *ᵥ x) (Br.iL hN) = x (Br.iL hN)) (G : Formalism.L2.DIV.VV K lam) :
    Br.brAt hN lam sg t (rhoVr emb lam γ' G) = rhoVr emb sg γ (Br.brAt hN lam sg t G) := by
  have hne : ∀ a : Fin n, Br.iC hN a ≠ Br.iL hN := fun a h => absurd (congrArg Fin.val h) a.2.ne
  have key := GlobalTheory.BranchFormula.equivariance K ι N n hN lam sg hI hS (invTrK (embGL emb γ)) (invTrK (embGL emb γ'))
    (fun τ => by
      simp only [invTrK_embGL_apply]
      refine ⟨fun a b => ?_, fun a => ⟨?_, ?_⟩, ?_⟩
      · have h := congrFun (h1 (Pi.single (Br.iC hN a) 1)) b
        have e : iniH hN (Pi.single (Br.iC hN a) (1 : E)) = Pi.single a 1 := by
          funext i
          simp only [iniH, Pi.single_apply, (Br.iC_inj hN).eq_iff]
        rw [e, mulVec_single_one, mulVec_single_one] at h
        exact congrArg _ h
      · have h := h2 (Pi.single (Br.iC hN a) 1)
        rw [mulVec_single_one, Pi.single_eq_of_ne (hne a).symm] at h
        exact (congrArg _ h).trans (map_zero _)
      · have h := congrFun (h1 (Pi.single (Br.iL hN) 1)) a
        have e : iniH hN (Pi.single (Br.iL hN) (1 : E)) = 0 := funext fun i => Pi.single_eq_of_ne (hne i) _
        rw [e, mulVec_zero, mulVec_single_one] at h
        exact (congrArg _ h).trans (map_zero _)
      · have h := h2 (Pi.single (Br.iL hN) 1)
        rw [mulVec_single_one, Pi.single_eq_same] at h
        exact (congrArg _ h).trans (map_one _)) G
  rw [Br.brAt, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
  exact congrArg _ key

variable [StarRing E] [StarRing K] (σ : K →+* ℂ)

theorem evV_rho {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (b : S.β) (g : S.G b) (v : Formalism.L2.DIV.VV K lam) :
    evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ (S.rho emb lam b g v) =
      S.tr emb σ b g (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) := by
  funext y
  have h : S.rho emb lam b g v = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) v := rfl
  rw [h, LinearMap.map_smulₛₗ, GStep.tr, trFr_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  refine evV_rhoVr_tr emb 1 lam σ _ v y _ ?_
  have := congrArg Subtype.val ((frEquiv emb σ (S.gam b g)).apply_symm_apply y)
  intro τ
  exact (congrFun this τ).symm


omit [NumberField E] [NumberField K] [StarRing E] [StarRing K] in
theorem polOf_evV {n : ℕ} (lam : ι → DomWeight n) (v : Formalism.L2.DIV.VV K lam) :
    polOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (evV emb (1 : Matrix (Fin n) (Fin n) E) lam σ v) =
      MvPolynomial.map σ v.1 := by
  have h := polOf_fnOf (Gr emb σ n) (shiftOf lam) (fr0 emb σ n) (MvPolynomial.map σ v.1)
  have e : (fun τ => ((fr0 emb σ n).1 τ)⁻¹) = 1 := funext fun τ => inv_one
  rwa [e] at h

variable {R : Ranks} {I : ChainIn E K ι R} (Q : PerIn I) (hc : ι → HCParam R)


omit [StarRing E] [StarRing K] in
theorem br_map (v : Formalism.L2.DIV.VV K (lamT hc R.m)) :
    Q.br emb σ hc (MvPolynomial.map σ v.1) =
      MvPolynomial.map σ (Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz) v).1 := by
  simp only [PerIn.br, Br.brAt, Br.brStd, LinearMap.smul_apply, LinearMap.comp_apply, Submodule.subtype_apply,
    Submodule.coe_smul, GlobalTheory.Proof.TensorMapDescent.branchingProjection_map]
  rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, map_prod σ]
  congr 2
  exact Finset.prod_congr rfl fun τ _ => (map_zpow₀ σ _ _).symm

theorem rho_mv_mem {n : ℕ} (S : GStep E K n) (lam : ι → DomWeight n) (h : (S.fam emb lam).Ok) (x : S.FormsK emb lam h)
    (hx : x ∈ (S.hlat emb lam h).L) (b : S.β) (d : S.D b) :
    S.rho emb lam b (S.mv b d) (x.1 (S.cl b d)) ∈ delAtr emb lam (S.Lsh b d) := by
  have h1 : delAtr emb lam (S.Lsh b (S.mv b d • S.rep (S.cl b d))) =
      (delAtr emb lam (S.Lsh b (S.rep (S.cl b d)))).map ((S.rho emb lam b (S.mv b d)).restrictScalars (𝓞 K)) :=
    (h b).del_smul (S.mv b d) (S.rep (S.cl b d))
  rw [S.mv_smul] at h1
  rw [h1]
  exact Submodule.mem_map_of_mem (hx (S.cl b d))

theorem exists_image (h6 : Formalism.MainNotions.PrimeDegreeVariant.Conclusion6) (hI : I.Ok) (hQ : Q.Ok)
    (hW : ∀ τ, Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ)) (hS : ∀ τ, Br.SameShift (lamT hc R.m τ) (Q.sgT τ))
    (hF : ((I.S R.m).fam emb (lamT hc R.m)).Ok) (hP : (Q.S'.fam emb Q.sgT).Ok)
    (x : (I.S R.m).FormsK emb (lamT hc R.m) hF) (hx : x ∈ ((I.S R.m).hlat emb (lamT hc R.m) hF).L) :
    ∃ y ∈ (Q.S'.hlat emb Q.sgT hP).L, Q.S'.embF emb σ Q.sgT hP y =
      (Q.per emb σ hI hQ hc).lowerMap ((Q.per emb σ hI hQ hc).evz ((I.S R.m).embF emb σ (lamT hc R.m) hF x)) := by
  let v : Q.S'.Cl → Formalism.L2.DIV.VV K (lamT hc R.m) := fun c =>
    (I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c))
  let B := Br.brAt (N_m_succ R) (lamT hc R.m) Q.sgT (fun τ => emb τ Q.tz)
  refine ⟨⟨fun c => B (v c), fun c g => ?_⟩, fun c => ?_, funext fun c => ?_⟩
  · have h1 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (((I.S R.m).mv Q.b0 (Q.tilPt c))⁻¹ * Q.ext c.1 g.1 *
        (I.S R.m).mv Q.b0 (Q.tilPt c)) (x.1 (Q.tilC c)) = x.1 (Q.tilC c) := x.2 (Q.tilC c) (Q.stabMap hQ c g)
    have h2 : (I.S R.m).rho emb (lamT hc R.m) Q.b0 (Q.ext c.1 g.1) (v c) = v c := by
      have h3 := congrArg ((I.S R.m).rho emb (lamT hc R.m) Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))) h1
      rw [← Module.End.mul_apply, ← map_mul, ← mul_assoc, mul_inv_cancel_left, map_mul, Module.End.mul_apply] at h3
      exact h3
    show ((Q.S'.chr c.1 g.1 : Kˣ) : K) • rhoVr emb Q.sgT (Q.S'.gam c.1 g.1) (B (v c)) = B (v c)
    rw [← brAt_rhoVr emb (N_m_succ R) hW hS _ (Q.S'.gam c.1 g.1) ((I.S R.m).gam Q.b0 (Q.ext c.1 g.1))
      (fun z => by rw [← map_inv, ← map_inv, ← map_inv]; exact hQ.gam_ini _ _ z)
      (fun z => by rw [← map_inv, ← map_inv]; exact hQ.gam_last _ _ z), ← map_smul, ← hQ.chr_ext]
    exact congrArg B h2
  · have h2 : v c ∈ delAtr emb (lamT hc R.m) ((I.S R.m).Lsh Q.b0 (Q.til c.1 (Q.S'.rep c))) :=
      rho_mv_mem emb (I.S R.m) (lamT hc R.m) hF x hx Q.b0 (Q.tilPt c)
    refine GlobalTheory.BranchFormula.integrality h6 K ι _ _ (N_m_succ R) _ _ hW hS _ _ (fun τ => (map_ne_zero _).2 hQ.tz_ne) _ ?_
    unfold delAtr at h2
    rwa [funext fun τ => dualFr_tauLat_sum emb (N_m_succ R) τ hQ.tz_ne _ _ (hQ.Lsh_til c.1 (Q.S'.rep c))] at h2
  · show _ = fnOf (Gr emb σ (R.N R.m - 1)) (shiftOf Q.sgT) 1 (Q.br emb σ hc
      (polOf (Gr emb σ (R.N R.m)) (shiftOf (lamT hc R.m)) (fr0 emb σ (R.N R.m))
        ((I.S R.m).tr emb σ Q.b0 ((I.S R.m).mv Q.b0 (Q.tilPt c))
          (evV emb (1 : Matrix (Fin (R.N R.m)) (Fin (R.N R.m)) E) (lamT hc R.m) σ (x.1 (Q.tilC c))))))
    rw [← evV_rho, polOf_evV, br_map]
    rfl


omit [StarRing K] in
theorem weights_ok (emb : ι → E →+* K) [StarRing K] (h : ∀ τ, Q.sg τ = (RowPar.of (hc τ)).sg) (τ : ι) :
    Br.Interlace (N_m_succ R) (lamT hc R.m τ) (Q.sgT τ) ∧ Br.SameShift (lamT hc R.m τ) (Q.sgT τ) := by
  classical
  let X : Fields := { F := ℚ, E := E, K := K, Tau := ι, emb := emb }
  let W : Wts X Unit R := ⟨fun τ => RowPar.of (hc τ), fun _ => hc, ∅⟩
  have := GlobalTheory.BranchMembers.members X Unit R W
    ⟨fun τ => ⟨hc τ, rfl⟩, fun _ _ => rfl, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩ () τ
  unfold PerIn.sgT
  rw [h τ]
  exact this

end General

variable {D : D7} {u : D.what₂.Word}

end GlobalTheory.LvT.BuiltChain
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsLocallyConstantToZModPow
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.Riemann

variable {p : ℕ} [Fact p.Prime]

noncomputable def resid (r n : ℕ) (x : Fin r → ℤ_[p]) : Fin r → ℕ :=
  fun j => (PadicInt.toZModPow n (x j)).val

theorem isLocallyConstant_toZModPow (n : ℕ) :
    IsLocallyConstant fun x : ℤ_[p] => PadicInt.toZModPow n x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hp : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.closedBall_mem_nhds x hp] with y hy
  rw [Metric.mem_closedBall, dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero] at hy
  exact hy

theorem isLocallyConstant_resid (r n : ℕ) : IsLocallyConstant (resid (p := p) r n) := by
  rw [IsLocallyConstant.iff_continuous]
  refine continuous_pi fun j => ?_
  exact (((isLocallyConstant_toZModPow (p := p) n).comp ZMod.val).comp_continuous
    (continuous_apply j)).continuous

theorem resid_mem (r n : ℕ) (x : Fin r → ℤ_[p]) :
    resid r n x ∈ Fintype.piFinset fun _ : Fin r => Finset.range (p ^ n) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  rw [Fintype.mem_piFinset]
  intro j
  exact Finset.mem_range.2 (ZMod.val_lt _)

theorem dist_resid (r n : ℕ) (x : Fin r → ℤ_[p]) :
    dist x (fun j => ((resid r n x j : ℕ) : ℤ_[p])) ≤ (p : ℝ) ^ (-n : ℤ) := by
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  have hp : (0 : ℝ) < (p : ℝ) ^ (-n : ℤ) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  rw [dist_pi_le_iff hp.le]
  intro j
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
  simp [resid]

noncomputable def ind (r n : ℕ) (a : Fin r → ℕ) : C(Fin r → ℤ_[p], ℂ_[p]) :=
  ⟨fun x => if resid r n x = a then 1 else 0,
    ((isLocallyConstant_resid (p := p) r n).comp fun b => if b = a then (1 : ℂ_[p]) else 0).continuous⟩

theorem norm_ind_le (r n : ℕ) (a : Fin r → ℕ) : ‖ind (p := p) r n a‖ ≤ 1 := by
  rw [ContinuousMap.norm_le _ zero_le_one]
  intro x
  show ‖if resid r n x = a then (1 : ℂ_[p]) else 0‖ ≤ 1
  split_ifs <;> simp

theorem riemann_sums : ∀ (p r : ℕ) [Fact p.Prime] (μ : C(Fin r → ℤ_[p], ℂ_[p]) →L[ℂ_[p]] ℂ_[p]) (I : Type) (g : I → C(Fin r → ℤ_[p], ℂ_[p])), ‖μ‖ ≤ 1 → InIntClosure (Set.univ : Set (Fin r → ℕ)) (fun a i => g i fun j => (a j : ℤ_[p])) Set.univ fun i => μ (g i) := by
  intro p r _ μ I g hμ F _ ε hε
  classical
  have hμ' : ∀ f, ‖μ f‖ ≤ ‖f‖ := fun f =>
    (μ.le_opNorm f).trans (mul_le_of_le_one_left (norm_nonneg _) hμ)
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hev : ∀ i, ∀ᶠ n : ℕ in Filter.atTop, ∀ x y : Fin r → ℤ_[p],
      dist x y ≤ (p : ℝ) ^ (-n : ℤ) → dist (g i x) (g i y) < ε / 2 := by
    intro i
    obtain ⟨δ, hδ, h⟩ := Metric.uniformContinuous_iff.1
      (CompactSpace.uniformContinuous_of_continuous (g i).continuous) (ε / 2) (half_pos hε)
    have ht : Filter.Tendsto (fun n : ℕ => ((p : ℝ)⁻¹) ^ n) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) (inv_lt_one_of_one_lt₀ hp1)
    filter_upwards [ht.eventually (gt_mem_nhds hδ)] with n hn x y hxy
    refine h (hxy.trans_lt ?_)
    rw [zpow_neg, zpow_natCast, ← inv_pow]
    exact hn
  obtain ⟨n, hn⟩ := ((Filter.eventually_all_finset F).2 fun i _ => hev i).exists
  set S : Finset (Fin r → ℕ) := Fintype.piFinset fun _ : Fin r => Finset.range (p ^ n) with hS
  refine ⟨Finsupp.onFinset S (fun a => if a ∈ S then μ (ind r n a) else 0)
    (fun a ha => by by_contra h; simp [h] at ha), Set.subset_univ _, ?_, ?_⟩
  · intro a
    rw [Finsupp.onFinset_apply]
    split_ifs
    · exact (hμ' _).trans (norm_ind_le r n a)
    · simp
  · intro i hi
    rw [Finsupp.onFinset_sum _ (by simp)]
    have h1 : (∑ a ∈ S, (if a ∈ S then μ (ind r n a) else 0) * g i fun j => (a j : ℤ_[p]))
        = μ (∑ a ∈ S, (g i fun j => (a j : ℤ_[p])) • ind r n a) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      rw [if_pos ha, map_smul, smul_eq_mul, mul_comm]
    beta_reduce
    rw [h1, ← map_sub]
    refine (hμ' _).trans_lt (lt_of_le_of_lt ?_ (half_lt_self hε))
    rw [ContinuousMap.norm_le _ (half_pos hε).le]
    intro x
    have h2 : (∑ a ∈ S, (g i fun j => (a j : ℤ_[p])) • ind r n a) x
        = g i fun j => ((resid r n x j : ℕ) : ℤ_[p]) := by
      rw [ContinuousMap.sum_apply, Finset.sum_eq_single (resid r n x)]
      · simp [ind]
      · intro b _ hb
        simp [ind, Ne.symm hb]
      · intro h
        exact absurd (resid_mem r n x) h
    rw [ContinuousMap.sub_apply, h2, ← dist_eq_norm]
    exact (hn i hi _ _ (dist_resid r n x)).le

end GlobalTheory.MomT.Riemann
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LatSumReindexOfLeSup
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory

theorem latSum_reindex_of_le_sup (E : Type) [Field E] [NumberField E] (W : Type) [AddCommGroup W] [Module (𝓞 E) W]
    (D C As B : Submodule (𝓞 E) W) (f g : W → ℂ) (hCD : C ≤ D) (hB : ∀ t ∈ As, t ∈ B ↔ t ∈ C) (hD : D ≤ As ⊔ C)
    (hfg : ∀ x ∈ D, ∀ t ∈ As, t - x ∈ C → f x = g t) (hg : ∀ t ∈ As, t ∉ D → g t = 0) :
    latSum D C f = latSum As B g := by
  classical
  unfold latSum
  set r : (↥D ⧸ C.comap D.subtype) → ↥D :=
    Function.surjInv (Submodule.Quotient.mk_surjective (C.comap D.subtype)) with hr
  set s : (↥As ⧸ B.comap As.subtype) → ↥As :=
    Function.surjInv (Submodule.Quotient.mk_surjective (B.comap As.subtype)) with hs
  have hr' : ∀ z, Submodule.Quotient.mk (r z) = z := fun z => Function.surjInv_eq _ z
  have hs' : ∀ z, Submodule.Quotient.mk (s z) = z := fun z => Function.surjInv_eq _ z
  have hex : ∀ x : ↥D, ∃ t : ↥As, (t : W) - x ∈ C := by
    intro x
    obtain ⟨a, ha, c, hc, h⟩ := Submodule.mem_sup.1 (hD x.2)
    refine ⟨⟨a, ha⟩, ?_⟩
    have : a - (x : W) = -c := by rw [← h]; abel
    simpa [this] using hc
  choose τ hτ using hex
  have keyA : ∀ t u : ↥As, (Submodule.Quotient.mk t : ↥As ⧸ B.comap As.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    exact hB _ (t - u).2
  have keyD : ∀ t u : ↥D, (Submodule.Quotient.mk t : ↥D ⧸ C.comap D.subtype) = Submodule.Quotient.mk u ↔ (t : W) - u ∈ C := by
    intro t u
    rw [Submodule.Quotient.eq, Submodule.mem_comap]
    rfl
  let φ : (↥D ⧸ C.comap D.subtype) → (↥As ⧸ B.comap As.subtype) := fun z => Submodule.Quotient.mk (τ (r z))
  have hφ : ∀ z, (s (φ z) : W) - r z ∈ C := by
    intro z
    have h1 : (s (φ z) : W) - τ (r z) ∈ C := (keyA _ _).1 (hs' _)
    have := C.add_mem h1 (hτ (r z))
    simpa using this
  have hinj : Function.Injective φ := by
    intro z w h
    rw [← hr' z, ← hr' w, keyD]
    have h1 := hφ z
    have h2 := hφ w
    rw [h] at h1
    have := C.sub_mem h2 h1
    simpa using this
  have e1 : ∑ᶠ z, f (r z : W) = ∑ᶠ z, (fun y => g (s y : W)) (φ z) :=
    finsum_congr fun z => hfg _ (r z).2 _ (s (φ z)).2 (hφ z)
  rw [e1, ← finsum_mem_range (f := fun y => g (s y : W)) hinj, ← finsum_mem_univ (fun y => g (s y : W))]
  apply finsum_mem_inter_support_eq'
  intro y hy
  simp only [Set.mem_univ, iff_true]
  have hyD : (s y : W) ∈ D := by
    by_contra h
    exact hy (hg _ (s y).2 h)
  refine ⟨Submodule.Quotient.mk ⟨_, hyD⟩, ?_⟩
  have h1 := hφ (Submodule.Quotient.mk ⟨_, hyD⟩)
  have h2 : (r (Submodule.Quotient.mk ⟨_, hyD⟩) : W) - s y ∈ C := (keyD _ ⟨_, hyD⟩).1 (hr' _)
  have h3 := C.add_mem h1 h2
  have h4 := (keyA (s (φ (Submodule.Quotient.mk ⟨_, hyD⟩))) (s y)).2 (by simpa using h3)
  rwa [hs', hs'] at h4

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ParametersWindowsOfExplicitParametersStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab GlobalTheory.EX NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.windows_of_explicitParameters : ∀ eps cD ch C8 : ℝ, 0 < eps → eps < 1 / 52 → 0 ≤ cD → 402 ≤ ch → ∃ x0 : ℝ, ∀ (s : Scale) (D : D7) (bT : D.host.TT → ℤ), s.eps = eps → x0 ≤ s.x → RankVal s D.R → HostVal s C8 D.host → (∀ t, s.b' ≤ (bT t : ℝ) ∧ (bT t : ℝ) ≤ 2 * s.b') → HCVal s cD ch D.host (fun τ => (D.eTau τ : D.R.GG)) D.hc bT → let η : ℝ := (D.R.m : ℝ) * (h0v s ch : ℝ); let S : ℝ := (D.R.k : ℝ) * (4 * (Delv s cD : ℝ)); (∀ τ (t : D.host.TT) (hm : 0 < D.R.m), (D.eTau τ : D.R.GG) = D.R.tau1 t → (((D.hc τ).b ⟨0, hm⟩ : ℚ) : ℝ) - (bT t : ℝ) > ((D.R.k : ℝ) - 1) / 2 + 3) ∧ (∀ τ j, (((D.hc τ).b j : ℚ) : ℝ) ≤ s.b ^ 2) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, (D.eTau τ : D.R.GG) ∈ D.host.thickPlaces → s.b ≤ wj D j τ ∧ wj D j τ ≤ s.b + η + 1) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → (bT t : ℝ) + s.b' / s.x ≤ wj D j τ ∧ wj D j τ ≤ (bT t : ℝ) + s.b' / s.x + η) ∧ (∀ j, 1 ≤ j → j ≤ D.R.m → ∀ τ, D.host.IsThin (D.eTau τ : D.R.GG) → s.w'' D.R.n ≤ wj D j τ ∧ wj D j τ ≤ s.w'' D.R.n + η) ∧ (∀ τ (h0 : 0 < D.R.k - 1), (D.eTau τ : D.R.GG) ∉ D.host.topPlaces → S ≤ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ∧ (((D.hc τ).u ⟨0, by omega⟩ - (D.hc τ).v ⟨0, h0⟩ : ℚ) : ℝ) ≤ 2 * S) ∧ (∀ τ (i : Fin (D.R.k - 1)), 0 ≤ (((D.hc τ).v i : ℚ) : ℝ) ∧ (((D.hc τ).v i : ℚ) : ℝ) ≤ S) ∧ (∀ τ (i j : Fin D.R.m), |(((D.hc τ).b i - (D.hc τ).e j : ℚ) : ℝ)| ≤ η) ∧ 1 ≤ (D.R.t : ℝ) ∧ (D.R.t : ℝ) ≤ s.x ^ (401 : ℝ) ∧ 10 * ⌈Real.logb 5 ((D.R.n : ℝ) * D.R.N D.R.m / D.R.m)⌉₊ + 20 ≤ D.host.Lw ∧ 0 < D.host.T2.card ∧ D.host.T2.card ≤ D.R.n := by
  first | exact @GlobalTheory.EX.windows_of_large_scale | exact GlobalTheory.EX.windows_of_large_scale | (intros; apply GlobalTheory.EX.windows_of_large_scale <;> assumption)
end

