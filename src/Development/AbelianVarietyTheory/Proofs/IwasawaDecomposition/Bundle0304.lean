module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StdLvPr
public import Formalism.LocalToGlobal.HermitianForms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0156
public import Formalism.LocalToGlobal.Columns.RecLevelLocT
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0116
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0124
public import Formalism.LocalToGlobal.HermitianForms.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0019
public import Formalism.LocalToGlobal.Columns.ToHLatLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0287
public import Formalism.LocalToGlobal.Columns.Bundle0001
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CongruenceLevelEqDepthSucc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0176
public import Formalism.LocalToGlobal.GroupLattices.LevelCharts.JoinForms
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.LocalToGlobal.IndefiniteReal.FrameExistence.InitialDataUntwistedOfModelChoice
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0290

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianStepLevelOfChartFormsLevel
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.Lv

section Build
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

theorem reL_rfl {a : ℕ} (L : Submodule (𝓞 E) (Fin a → E)) : reL (rfl : a = a) L = L := by
  ext x
  simp [reL, reV, LinearEquiv.funCongrLeft, LinearMap.funLeft]

theorem reGL_rfl_map {a : ℕ} {R : Type} [CommRing R] (U : Subgroup (GL (Fin a) R)) :
    U.map (reGL (rfl : a = a) R).toMonoidHom = U := by
  have : ∀ x, reGL (rfl : a = a) R x = x := fun x => by
    ext i j
    simp [reGL]
  ext x
  simp [Subgroup.mem_map, this]

theorem exists_herm_level (hc : CMData F E) (S : HSpace E) {n : ℕ} (h : S.rank = n) (gp : Fin 2 → ℕ) (T f : ℕ)
    {bad : Set (HeightOneSpectrum (𝓞 F))} {J : Matrix (Fin n) (Fin n) E} (hJ : J = S.gram.reindex (finCongr h) (finCongr h))
    (K : StepLevel F E hc.sig J T f bad)
    (hbad : ∀ v : HeightOneSpectrum (𝓞 F), (gp 0 : 𝓞 F) ∉ v.asIdeal → (gp 1 : 𝓞 F) ∉ v.asIdeal → v ∉ bad)
    (hg : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → ∀ x ∈ levelVL hc.sig J v K.Lb,
      (∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb, ∃ z ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb,
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y = ((gp a : ℕ) : E ⊗[F] v.adicCompletion F) • z) → x ∈ K.Uloc v)
    (hT : ∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∈ v.asIdeal → ∀ x, x ∈ K.Uloc v ↔ x ∈ levelVL hc.sig J v K.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (hc.sig : E →+* E) J K.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) K.Lb) :
    ∃ L : Formalism.L2.Herm.StepLevel hc S gp T f, K.Lb = reL h L.Lb ∧
      (∀ v, K.Uloc v = (L.Uloc v).map (reGL h _).toMonoidHom) ∧ K.U = L.U.map (reGL h _).toMonoidHom := by
  subst h
  have hJ' : J = S.gram := by rw [hJ]; ext a b; simp
  subst hJ'
  clear hJ
  refine ⟨{ Lb := K.Lb, Lb_fin := K.Lb_fin, Lb_span := K.Lb_span, Lb_int := fun x hx => Submodule.subset_span (K.Lb_int x hx),
            Lb_dual := ?_, Lb_index := K.Lb_index, Uloc := K.Uloc, Uloc_lev := K.Uloc_lev, Uloc_hyp := ?_, Uloc_g := ?_, UlocAlt := ?_,
            U := K.U, U_eq := K.U_eq }, ?_, ?_, ?_⟩
  · intro y hy
    unfold Formalism.L2.Herm.dualL at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact K.Lb_dual y hy
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact add_mem ha hb
    | smul s a _ ha => rw [smul_comm]; exact Submodule.smul_mem _ _ ha
  · intro v h0 h1 h2
    exact K.Uloc_hyp v (hbad v h0 h1) h2
  · intro a v h x hx
    exact hg a v h x hx.1 hx.2
  · intro v h x
    exact hT v h x
  · exact (reL_rfl _).symm
  · intro v; exact (reGL_rfl_map _).symm
  · exact (reGL_rfl_map _).symm

end Build
end GlobalTheory.Mem.Col2.Lv

namespace GlobalTheory.Mem.Col2.Lv
section W
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem uloc_T_iff (σ : E →ₐ[F] E) (hdeg : Module.finrank F E = 2) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x → x ∈ (algebraMap F E).range)
    (hun : ∀ P : Ideal (𝓞 E), P.IsMaximal → ∃ θ t : 𝓞 E, (t : E) = σ θ ∧ θ - t ∉ P) {n : ℕ} [NeZero n] {J : Matrix (Fin n) (Fin n) E} (hJ : J = 1)
    {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 F))} (S : StepLevel F E σ J T f bad) (p q : 𝓞 E) (hq : (q : E) = σ (p : E))
    (hpq : (p : E) * (q : E) = (T : E)) (hT : T.Prime) (hL : S.Lb = rll_dLat n ((p : E)⁻¹))
    (v : HeightOneSpectrum (𝓞 F)) (hv : (T : 𝓞 F) ∈ v.asIdeal)
    (hunif : ∀ a : v.adicCompletionIntegers F, Valued.v (a : v.adicCompletion F) < 1 → ∃ b : v.adicCompletionIntegers F, a = (T : v.adicCompletionIntegers F) * b)
    (x : GL (Fin n) (E ⊗[F] v.adicCompletion F)) :
    x ∈ S.Uloc v ↔ x ∈ levelVL σ J v S.Lb ∧
      ∀ y ∈ latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (σ : E →+* E) J S.Lb)),
        (x : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) *ᵥ y - y ∈ latS (F := F) (v.adicCompletion F) (intV E v) S.Lb := by
  subst hJ
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.2 hT.ne_zero
  have hp0 : (p : E) ≠ 0 := fun h => hT0 (by rw [← hpq, h, zero_mul])
  refine ⟨fun hx => ⟨S.Uloc_lev v hx, GlobalTheory.T.level_acts_trivially_on_discriminant_group σ hσ S p q hq hpq hT.ne_zero hL ?_ v hv ?_ x hx⟩, fun h => GlobalTheory.uloc_of_triv_disc σ S v hv x h.1 h.2⟩
  · rw [hL]; exact GlobalTheory.uLocDual_eq σ hσ n p q hp0 hq
  · intro m hm d c hd hc
    exact _root_.GlobalTheory.UnitaryScalarModT.eq_one_add_of_fixes σ hdeg hσ hfix hun v T hT hunif (S.fM v hv) (S.fM_card v hv) m hm d c hd hc

end W

theorem baseL_eq (B : Base) (n : ℕ) [NeZero n] (t : 𝓞 B.host.E) (ht : (t : B.host.E) ≠ 0) (L : Submodule (𝓞 B.host.E) (Fin n → B.host.E))
    (h : ∀ x, x ∈ L ↔ x ∈ baseL B n t) : L = rll_dLat n ((t : B.host.E)⁻¹) := by
  have hlast : ∀ j : Fin n, j.1 + 1 = n ↔ j = lastIdx n := by
    intro j
    have := NeZero.pos n
    constructor
    · intro e; apply Fin.ext; simp [lastIdx]; omega
    · intro e; rw [e]; simp [lastIdx]; omega
  ext x
  rw [h, rll_mem_dLat]
  constructor
  · intro hx
    refine ⟨fun i _ => ?_, ?_⟩
    · obtain ⟨r, e, -⟩ := hx i
      exact ⟨r, e.symm⟩
    · obtain ⟨r, e, hd⟩ := hx (lastIdx n)
      obtain ⟨c, rfl⟩ := hd ((hlast _).2 rfl)
      refine ⟨c, ?_⟩
      rw [e]
      show _ = _ * algebraMap (𝓞 B.host.E) B.host.E (t * c)
      rw [map_mul]
      exact (inv_mul_cancel_left₀ ht _).symm
  · rintro ⟨h1, c, hc⟩ j
    by_cases hj : j = lastIdx n
    · subst hj
      refine ⟨t * c, ?_, fun _ => dvd_mul_right _ _⟩
      have e : x (lastIdx n) = (t : B.host.E) * (c : B.host.E) := by
        have : algebraMap (𝓞 B.host.E) B.host.E c = (t : B.host.E)⁻¹ * x (lastIdx n) := hc
        show _ = _
        rw [show (c : B.host.E) = algebraMap (𝓞 B.host.E) B.host.E c from rfl, this, mul_inv_cancel_left₀ ht]
      rw [e]; rfl
    · obtain ⟨r, hr⟩ := h1 j hj
      exact ⟨r, hr.symm, fun e => absurd ((hlast j).1 e) hj⟩

end GlobalTheory.Mem.Col2.Lv


set_option maxHeartbeats 2000000 in
theorem GlobalTheory.Mem.Col2.TC.level_of_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) {Ch : ℕ → Type} {chOf : ∀ i, ((I.rec7 l Z).mem u).C.cls i → Ch i} (F : FormsTiedSym (I.rec7 l Z) u Ch chOf), I.StdF l Z u F → ∀ (i : ℕ) (hi : i ≤ (I.rec7 l Z).R.m) {cl : Type} {stab : cl → Type} [∀ c, Group (stab c)]
  {lat : cl → Submodule (𝓞 (I.rec7 l Z).host.E) (Fin ((I.rec7 l Z).R.N i) → (I.rec7 l Z).host.E)}
  (K : LevelChart (I.rec7 l Z) ((I.rec7 l Z).mem u).A.T (badG (I.rec7 l Z)) i hi stab lat)
  {Hs : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), ((I.rec7 l Z).host.g a : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin ((I.rec7 l Z).R.N i)) (kv (I.rec7 l Z).host.F v))} {lam : ∀ a v h, Hs a v h →* ℂˣ},
  GLevH K.lev F.gl Hs lam → (∀ x, x ∈ K.lev.Lb ↔ x ∈ baseL B ((I.rec7 l Z).R.N i) (X.piT u)) →
  ∃ L : Formalism.L2.Herm.StepLevel (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (I.rec7 l Z).host.g ((I.rec7 l Z).mem u).A.T (I.rec7 l Z).R.f,
    K.lev.Lb = reL (rankN (I.rec7 l Z) i hi) L.Lb ∧
    (∀ v, K.lev.Uloc v = (L.Uloc v).map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom) ∧
    K.lev.U = L.U.map (reGL (rankN (I.rec7 l Z) i hi) _).toMonoidHom := by
  intro B X I hI hP l Z u Ch chOf F hF i hi cl stab _ lat K Hs lam hG hLb
  have hgram : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hI hP l Z).2.2.2 i hi).1
  haveI : NeZero ((I.rec7 l Z).R.N i) := ⟨by
    have := (I.rec7 l Z).R.m_add_three_le_k
    simp only [Ranks.N]; omega⟩
  let s : 𝓞 (I.rec7 l Z).host.E →+* 𝓞 (I.rec7 l Z).host.E := RingOfIntegers.mapRingHom (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E)
  have hsc : ∀ x, (s x : (I.rec7 l Z).host.E) = (I.rec7 l Z).host.conj (x : (I.rec7 l Z).host.E) := fun x => Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.forms_involution_eq_host_conj _
  have hpq : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) * (s F.atT.piU : (I.rec7 l Z).host.E) = (((I.rec7 l Z).mem u).A.T : (I.rec7 l Z).host.E) := by
    rw [hsc]; exact F.atT.piU_norm
  have hTp := ((I.rec7 l Z).mem u).A.T_prime
  have hp0 : ((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E) ≠ 0 := fun h => (Nat.cast_ne_zero.2 hTp.ne_zero) (by rw [← hpq, h, zero_mul])
  have hL : K.lev.Lb = rll_dLat ((I.rec7 l Z).R.N i) (((F.atT.piU : 𝓞 (I.rec7 l Z).host.E) : (I.rec7 l Z).host.E)⁻¹) := by
    refine GlobalTheory.Mem.Col2.Lv.baseL_eq B _ F.atT.piU hp0 K.lev.Lb ?_
    rw [hF.piU]; exact hLb
  refine GlobalTheory.Mem.Col2.Lv.exists_herm_level (I.rec7 l Z).sp.cm ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (I.rec7 l Z).host.g _ _ rfl K.lev ?_ ?_ ?_
  · intro v h0 h1 hb
    rcases hb with hb | hb
    · exact h0 hb
    · exact h1 hb
  · intro a v h x hx hp
    exact GlobalTheory.Mem.LevCong.mem_Uloc_of_cong _ K.lev F.gl hG a v h x hx hp
  · intro v h x
    exact GlobalTheory.Mem.Col2.Lv.uloc_T_iff (sigD (I.rec7 l Z)) (I.rec7 l Z).sp.cm.deg2 (fun x => star_star x) (fun x hx => ((I.rec7 l Z).sp.cm.fixed x).1 hx)
      (I.rec7 l Z).sp.cm.cmUnram.2.2 hgram K.lev F.atT.piU (s F.atT.piU) rfl hpq hTp hL v h (_root_.GlobalTheory.LevelUnif.dvd_of_val_lt_one (I.rec7 l Z) u F.atT v h) x

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqOfNormSq
section
noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions _root_.Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000

theorem inner_eq_of_norm_sq {K V E M : Type} [Field K] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup M] [Module K M] (σ : K →+* ℂ) (j : M →ₛₗ[σ] V) (hspan : Submodule.span ℂ (Set.range j) = ⊤) (k : K)
    (hk : (σ k).im ≠ 0) (e : V →ₗ[ℂ] E) (q : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hn : ∀ m, ((‖e (j m)‖ ^ 2 : ℝ) : ℂ) = q (j m) (j m))
    (y y' : V) : inner ℂ (e y) (e y') = q y y' := by
  let D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun y y' => inner ℂ (e y) (e y') - q y y')
    (fun y z y' => by simp only [map_add (f := _), inner_add_left, LinearMap.add_apply]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_left, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun y y' z => by simp only [map_add (f := _), inner_add_right]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring)
  have hDapp : ∀ y y', D y y' = inner ℂ (e y) (e y') - q y y' := fun y y' => rfl
  have h0 : ∀ m, D (j m) (j m) = 0 := by
    intro m
    rw [hDapp, ← hn m, inner_self_eq_norm_sq_to_K]
    simp
  have hsym : ∀ m m', D (j m) (j m') + D (j m') (j m) = 0 := by
    intro m m'
    have h := h0 (m + m')
    simp only [map_add (f := _), LinearMap.add_apply, h0 m, h0 m'] at h
    linear_combination h
  have hpair : ∀ m m', D (j m) (j m') = 0 := by
    intro m m'
    have h1 := hsym m (k • m')
    rw [j.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
    have h2 := hsym m m'
    have h3 : (σ k - starRingEnd ℂ (σ k)) * D (j m) (j m') = 0 := by linear_combination h1 - starRingEnd ℂ (σ k) * h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exfalso
      rw [Complex.sub_conj] at h4
      simp [hk] at h4
    · exact h4
  have h1 : ∀ m, D (j m) = 0 := fun m => LinearMap.ext_on_range hspan fun m' => by rw [hpair m m']; rfl
  have hall : D = 0 := LinearMap.ext_on_range hspan fun m => by rw [h1 m]; rfl
  have h := congrArg (fun D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => D y y') hall
  simp only [hDapp, LinearMap.zero_apply] at h
  exact sub_eq_zero.1 h

theorem exists_embLL_im_ne {B : Base} (hX : B.fields.Ok) : ∃ k : B.LL, (B.embLL k).im ≠ 0 := by
  have hc : (InfinitePlace.mk (B.embLL : B.fields.K →+* ℂ)).IsComplex := hX.cplxK.isComplex _
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  by_contra hne
  push_neg at hne
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hne x)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def cjPol (ι : Type) (n : ℕ) : Pol ℂ ι n →ₗ⋆[ℂ] Pol ℂ ι n where
  toFun p := MvPolynomial.map (starRingEnd ℂ) p
  map_add' p q := map_add _ p q
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, RingHom.id_apply]

theorem map_conj_smul {ι : Type} {n : ℕ} (r : ℂ) (p : Pol ℂ ι n) :
    MvPolynomial.map (starRingEnd ℂ) (r • p) = starRingEnd ℂ r • MvPolynomial.map (starRingEnd ℂ) p :=
  (cjPol ι n).map_smulₛₗ r p

abbrev rowS (a : I.ι) : GSD B.fields.K := mtildeGSD (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps

theorem rowS_ok (hX : B.fields.Ok) (a : I.ι) : (rowS I a).Ok :=
  mtildeOk (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) hX I.Ps

def cTerm (a : I.ι) (c : (rowS I a).Cl) (F G : MtCx I a) : ℂ :=
  ((Nat.card (@MulAction.stabilizer (rowS I a).G (rowS I a).D _ (rowS I a).actD ((rowS I a).outSec.rep c)) : ℕ) : ℂ)⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 ((rowS I a).outSec.rep c))) (G.1 ((rowS I a).outSec.rep c))

theorem cTerm_add_left (a : I.ι) (c : (rowS I a).Cl) (F F' G : MtCx I a) :
    cTerm I a c (F + F') G = cTerm I a c F G + cTerm I a c F' G := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add (f := _), LinearMap.add_apply, mul_add]

theorem cTerm_smul_left (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c (r • F) G = starRingEnd ℂ r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_conj_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem cTerm_add_right (a : I.ι) (c : (rowS I a).Cl) (F G G' : MtCx I a) :
    cTerm I a c F (G + G') = cTerm I a c F G + cTerm I a c F G' := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add (f := _), mul_add]

theorem cTerm_smul_right (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c F (r • G) = r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_smul, smul_eq_mul]
  ring

def cSum (hX : B.fields.Ok) (a : I.ι) : MtCx I a →ₗ⋆[ℂ] MtCx I a →ₗ[ℂ] ℂ :=
  letI := (rowS_ok I hX a).fintypeCl
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun F G => ∑ c : (rowS I a).Cl, cTerm I a c F G)
    (fun F F' G => by simp only [cTerm_add_left, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_left, Finset.mul_sum, smul_eq_mul])
    (fun F G G' => by simp only [cTerm_add_right, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])

theorem cSum_apply (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) :
    cSum I hX a F G = letI := (rowS_ok I hX a).fintypeCl; ∑ c : (rowS I a).Cl, cTerm I a c F G := rfl

end GlobalTheory.Mem.Df

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntegralFormsHermLatticeGoodAndComplexBasis
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Df
attribute [local instance] GlobalTheory.Mem.Col2.starE

namespace GlobalTheory.Mem.Df

theorem toCx_smul {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (c : B.LL) (x : (MtHL I hX a).V) :
    toCx I hX a (c • x) = B.embLL c • toCx I hX a x := by
  have h1 : toCx I hX a (c • x) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      (c • (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x)) := rfl
  rw [h1, LinearMap.map_smulₛₗ]
  rfl

theorem toCx_add {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) (x y : (MtHL I hX a).V) :
    toCx I hX a (x + y) = toCx I hX a x + toCx I hX a y := by
  have h1 : toCx I hX a (x + y) = toMtP B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL
      ((show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from x) + (show MtildeV B.wts I.Ch I.sel (I.tup a) I.Ps from y)) := rfl
  rw [h1, map_add (f := _)]
  rfl

noncomputable def toCxₛₗ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a where
  toFun := toCx I hX a
  map_add' := toCx_add I hX a
  map_smul' := toCx_smul I hX a

theorem toCx_linearIndependent {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) :=
  toMtilde_linearIndependent _ _ _ _ _ _ (MtHL I hX a).b.linearIndependent

theorem toCx_span {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) :
    Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  rw [eq_top_iff, ← toMtilde_span B.wts I.Ch I.sel (I.tup a) I.Ps B.embLL hX, Submodule.span_le]
  rintro _ ⟨x, rfl⟩
  have hle : Submodule.span B.LL (Set.range (MtHL I hX a).b) ≤
      Submodule.comap (toCxₛₗ I hX a) (Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i))) := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨i, rfl⟩
  rw [(MtHL I hX a).b.span_eq] at hle
  exact hle (Submodule.mem_top (x := (x : (MtHL I hX a).V)))

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι) : (MtHL I hX a).Good :=
  MtildeH_good _ _ _ _ _ _
end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

theorem mtHL_good_basis : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X) (hX : B.fields.Ok) (a : I.ι), (MtHL I hX a).Good ∧ (∃ j : (MtHL I hX a).V →ₛₗ[B.embLL] MtCx I a, ∀ x, j x = toCx I hX a x) ∧ LinearIndependent ℂ (fun i => toCx I hX a ((MtHL I hX a).b i)) ∧ Submodule.span ℂ (Set.range fun i => toCx I hX a ((MtHL I hX a).b i)) = ⊤ := by
  intro B X I hX a
  refine ⟨?_, ⟨{ toFun := toCx I hX a, map_add' := fun x y => ?_, map_smul' := fun c x => ?_ }, fun _ => rfl⟩,
    toCx_linearIndependent I hX a, toCx_span I hX a⟩
  · exact mtHL_good I hX a
  · exact toCx_add I hX a x y
  · exact toCx_smul I hX a c x

end GlobalTheory.Mem.Df
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IpMtTie
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.IpMt

theorem ipMt_tie : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (jM : (I.per l u a).Mt →ₛₗ[starRingEnd ℂ] (I.per l u a).Wrow), (∀ F, jM F ∈ (I.fm l u a).ptC) → (∀ w F, (I.per l u a).period w F = (I.fm l u a).ipP (jM F) w) → (∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F)) ∧ ∀ F, F ≠ 0 → 0 < (I.ipMt l u a F F).re := by
  intro B X I hOk hP l Z u a jM hmem hper
  obtain ⟨j0, hinj, -, hmem0, hper0, hpos⟩ := PerConj.period_conj I hOk hP l Z u a
  have uniq : ∀ z ∈ (I.fm l u a).ptC, ∀ z' ∈ (I.fm l u a).ptC,
      (∀ w, (I.fm l u a).ipP z w = (I.fm l u a).ipP z' w) → z = z' := by
    intro z hz z' hz' h
    by_contra hne
    have h1 := hpos _ (sub_mem hz hz') (sub_ne_zero.2 hne)
    rw [map_sub (I.fm l u a).ipP, LinearMap.sub_apply, h, sub_self] at h1
    simp at h1
  have hj : ∀ G, I.jStd l u a G = jM G := by
    intro G
    have hex : ∃ z, z ∈ (I.fm l u a).ptC ∧ ∀ w, (I.per l u a).period w G = (I.fm l u a).ipP z w :=
      ⟨jM G, hmem G, fun w => hper w G⟩
    have hs := Classical.epsilon_spec hex
    exact uniq _ hs.1 _ (hmem G) fun w => (hs.2 w).symm.trans (hper w G)
  have hform : ∀ F G, I.ipMt l u a F G = (I.fm l u a).ipP (jM G) (jM F) := by
    intro F G
    rw [TC.ipMt, hj, hj]
  refine ⟨hform, fun F hF => ?_⟩
  have h0 : jM F = j0 F := uniq _ (hmem F) _ (hmem0 F) fun w => (hper w F).symm.trans (hper0 w F)
  have hne : jM F ≠ 0 := by
    rw [h0]
    exact fun h => hF (hinj (h.trans (map_zero j0).symm))
  rw [hform]
  exact hpos _ (hmem F) hne

theorem ipMt_sum {B : Base} {X : PreX B.toPre} (I : TC B X) (hOk : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l))
    (u : B.Word) (a : I.ι) (F G : (I.perIn u a).Mt B.fields.emb B.embLL) :
    I.ipMt l u a F G = letI := (I.perIn u a).clFin (l.per u a);
      ∑ c, (I.perIn u a).wt c * pairB (I.perIn u a).sgT
        (MvPolynomial.map (starRingEnd ℂ) (F.1 c.1 ((I.perIn u a).S'.rep c))) (G.1 c.1 ((I.perIn u a).S'.rep c)) := by
  have hE : ∀ τ x, embAt B.embLL B.fields.emb τ (letI := B.fields.starE; star x) =
      starRingEnd ℂ (embAt B.embLL B.fields.emb τ x) := fun τ x => (GlobalTheory.Mem.FieldsLaws.fields_ok B).conjE _ x
  have hH : ∀ b, (I.perIn u a).H b = ⊤ := fun _ => rfl
  have h := (ipMt_tie I hOk hP l Z u a (PerConj.jM (I.perIn u a) B.fields.emb B.embLL)
    (PerConj.jM_mem _ _ hE (l.per u a) hH)
    (PerConj.period_eq _ _ (l.ch u a) (l.per u a) (B.hcW u))).1 F G
  refine h.trans ?_
  refine (PerConj.petersson_apply B.fields.emb B.embLL (l.per u a) _ _).trans ?_
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  exact (PerConj.ipVal_cev _ _ _ _ _).trans (congrArg (fun p => pairB _ p _) (PerConj.polOf_cev _ _ _ _))

end GlobalTheory.Mem.Col2.IpMt

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemHJsymIffJSymG
section
open Formalism.L2.Col

namespace GlobalTheory

theorem mem_HJsym_iff_JSymG : ∀ (κ : Type) [Field κ] (n k r t m rS : ℕ) (h : r ≤ n), r = k + 2 * rS + 1 → 0 < t → n = r + m * t →
    ∀ M : GL (Fin n) κ, M ∈ HJsym κ n k r t m rS h ↔ M ∈ Formalism.L2.Forms.JSymG κ n k rS t false := by
  intro κ _ n k r t m rS h hr ht hn M
  subst hr
  rw [HJsym_eq_JSymG ht (by omega) h]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ModelsSeed
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ChainModels

theorem models_seed : GlobalTheory.Published.DiscreteSeriesExists → ∀ D : D7, HostHyp D → Formalism.IndefR.Seed.ModY D ∧
    ∀ (Ks : Type) [Field Ks] [Algebra Ks D.what₂.LL], (∀ x : D.host.E, ∃ y : Ks, algebraMap Ks D.what₂.LL y = D.embE x) →
      ∃ MW : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), DSModel (Wc D i) (parAt (Wc D i) σ),
        Formalism.IndefR.Seed.ModWAt D.what₂.embLL MW ∧ GlobalTheory.RealGeo.FrameKs Ks MW := by
  intro h D _
  exact exists_models h D

end GlobalTheory.ChainModels
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotTwistPlaceReferenceTuple
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.TC

theorem not_underQ_mu0 : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ v : HeightOneSpectrum (𝓞 B.host.F), ¬ I.UnderQ I.mu0 v := by
  intro B X I _ v ⟨P, hP, _⟩
  have e : P ∈ (∅ : Finset (HeightOneSpectrum (𝓞 B.fields.E))) := I.twistPrimes_reference_tuple_eq_empty ▸ hP
  simp at e

end GlobalTheory.Mem.Col2.TC
end

