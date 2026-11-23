module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetModuleFiniteLength
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0539
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0618
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PrincipalSeriesSupport.PrinSeriesWord
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0191
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0349
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0651
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FineJacquetSegmentLengthTwo
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0581
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0535
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0537
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Bundle0005
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.KSchur
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0012
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.FdConsA
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.Bundle0013
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0667
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0554
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.WeilThetaConvergence
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0212
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IrreducibleSubSegmentProduct
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
open GlobalTheory.Parabolic (Embeds)

namespace GlobalTheory.CompanionTheory.SegUniq

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_ne_zero_of_injective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Injective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hρ
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  exact ⟨v, fun e => hv (hφ (e.trans (map_zero φ).symm))⟩

theorem exists_ne_zero_of_surjective {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (φ : ρ.IntertwiningMap σ) (hφ : Function.Surjective φ) : ∃ v, φ v ≠ 0 := by
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hφ u
  exact ⟨v, hu⟩

theorem bot_ne_top_of_isSubquotient {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hσ : σ.IsIrreducible)
    (h : IsSubquotient σ ρ) : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
  obtain ⟨S, f, hf⟩ := h
  intro hb
  haveI := Model.nontrivial_of_isIrreducible hσ
  obtain ⟨u, hu⟩ := exists_ne (0 : W)
  obtain ⟨v, rfl⟩ := hf u
  have hv : (v : V) ∈ (⊥ : Subrepresentation ρ) := hb ▸ trivial
  have hv0 : v = 0 := Subtype.ext hv
  exact hu (by rw [hv0, map_zero])

theorem fineJac_all (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation)
    (Δ : Segment k) : FineJac Δ := by
  induction h : Δ.len using Nat.strong_induction_on generalizing Δ with
  | _ n ih =>
    have h0 := Δ.len_pos
    obtain h1 | h2 | h3 : n = 1 ∨ n = 2 ∨ 3 ≤ n := by omega
    · exact @GlobalTheory.T.fine_jacquet_length_one k _ _ _ _ hA Δ (h.trans h1)
    · exact @_root_.GlobalTheory.CompanionTheory.SegFine2.fineJac_of_len_eq_two k _ _ _ _ hA hZ Δ (h.trans h2)
    · exact @GlobalTheory.T.fine_jacquet_segment_induction k _ _ _ _ hA Δ (h ▸ h3) fun Δ' hlt => ih _ (h ▸ hlt) Δ' rfl

theorem exists_eq_of_embeds_one {c : ℕ} (hc : c = 1) (x : Fin c → IrrGL (k := k)) (y : IrrGL (k := k))
    (hd : ∑ a, (x a).1 = y.1) (φ : y.rep.IntertwiningMap (prodIrr x hd)) (hφ : Function.Injective φ) :
    ∃ a, y = x a := by
  subst hc
  obtain ⟨z, rfl⟩ : ∃ z, x = fun _ => z := ⟨x 0, funext fun a => by rw [Subsingleton.elim a 0]⟩
  refine ⟨0, ?_⟩
  obtain ⟨n, c⟩ := y
  obtain ⟨m, c'⟩ := z
  have hnm : m = n := by simpa using hd
  subst hnm
  obtain ⟨ψ⟩ := nonempty_equiv_prodIrr_one (⟨m, c'⟩ : IrrGL (k := k)) hd
  have hS := (isSocle_self (⟨m, c'⟩ : IrrGL (k := k)).2.rep.irr).of_equiv (.refl _) ψ
  obtain ⟨a⟩ := hS.equiv_of_embeds (⟨m, c⟩ : IrrGL (k := k)).2.rep.irr ⟨φ, hφ⟩
  exact congrArg (Sigma.mk m) (irrCl_eq_iff.2 ⟨a⟩)

theorem sum_concat_fst {s N : ℕ} (y : Fin s → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) (c : Fin s → ℕ)
    (x : ∀ a, Fin (c a) → IrrGL (k := k)) (hx : ∀ a, ∑ i, (x a i).1 = (y a).1) :
    ∑ i, (concat c x i).1 = N := by
  have h1 : ∑ i, (concat c x i).1 = ∑ p : Σ a, Fin (c a), (x p.1 p.2).1 :=
    Equiv.sum_comp finSigmaFinEquiv.symm (fun p : Σ a, Fin (c a) => (x p.1 p.2).1)
  rw [h1, Fintype.sum_sigma, ← hy]
  exact Finset.sum_congr rfl fun a _ => hx a

theorem eq_dec_of_one_le_jm (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {Δ : Segment k} (fine : FineJac Δ) {N : ℕ}
    {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V) (hL : IsLSeg Δ π)
    (hs : IsSmooth π) (hi : π.IsIrreducible) (y : Fin Δ.len → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N)
    (hpos : ∀ a, 0 < (y a).1) (h1 : 1 ≤ jm y hy π) : y = dec Δ := by
  have hemb := fun a => _root_.GlobalTheory.CompanionTheory.SubEmb.subEmbedding k (y a).1 _ (y a).rep (y a).2.rep.smooth (y a).2.rep.irr
  choose c x hx hcusp φ hφ using hemb
  have hne : ∀ a, ∃ v, φ a v ≠ 0 := fun a =>
    exists_ne_zero_of_injective (y a).2.rep.irr (φ a) (hφ a)
  have hjm : ∀ a, 1 ≤ jm (x a) (hx a) (y a).rep := fun a =>
    GlobalTheory.CompanionTheory.FrobJm.one_le_jm hA (x a) (hx a) (y a).rep (y a).2.rep.smooth (φ a) (hne a)
  have hcat := sum_concat_fst y hy c x hx
  have hle := GlobalTheory.T.jacquet_multiplicity_concat hA y hy c x hx hcat hjm π hs (hasFiniteLength_of_isIrreducible hi)
  have hcc : ∀ i, (concat c x i).IsCusp := fun i => hcusp _ _
  obtain ⟨hlen, -⟩ := (fine π hL).2 _ (concat c x) hcat hcc (h1.trans hle)
  have hc1 : ∀ a, 1 ≤ c a := fun a => by
    by_contra hc
    have hc0 : c a = 0 := by omega
    have h2 := hx a
    have h3 := hpos a
    have : IsEmpty (Fin (c a)) := by rw [hc0]; infer_instance
    rw [Fintype.sum_empty] at h2
    omega
  have hsum : ∑ a : Fin Δ.len, 1 = ∑ a, c a := by simpa using hlen.symm
  have hc : ∀ a, c a = 1 := fun a =>
    ((Finset.sum_eq_sum_iff_of_le fun a _ => hc1 a).1 hsum a (Finset.mem_univ a)).symm
  have hyc : ∀ a, (y a).IsCusp := fun a => by
    obtain ⟨b, hb⟩ := exists_eq_of_embeds_one (hc a) (x a) (y a) (hx a) (φ a) (hφ a)
    exact hb ▸ hcusp a b
  obtain ⟨h, hdec⟩ := (fine π hL).2 _ y hy hyc h1
  exact funext fun a => by simpa using hdec a

theorem isLSeg_of_dec : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hZ : GlobalTheory.Published.SegmentRepresentation) (Δ : Segment k) {N : ℕ}
    (hd : ∑ a, (dec Δ a).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth τ) (hi : τ.IsIrreducible)
    (f : τ.IntertwiningMap (prodIrr (dec Δ) hd)) (hf : Function.Injective f), IsLSeg Δ τ := by
  intro k _ _ _ _ hA hZ Δ N hd V _ _ τ hs hi f hf
  have fine : FineJac Δ := @fineJac_all k _ _ _ _ hA hZ Δ
  obtain ⟨L, hL⟩ := _root_.GlobalTheory.CompanionTheory.SegExists.exists_isLSeg hA Δ
  have hN : Δ.deg = N := by
    rw [← hd]
    show Δ.deg = ∑ _ : Fin Δ.len, Δ.d
    simp [Segment.deg]
  subst hN
  have hone := (fine L.ρ hL).1 hd
  let e := stdBlocks (fun a => (dec Δ a).1) hd
  have hfl : HasFiniteLength (GlobalTheory.SmGL.jac e L.ρ) :=
    GlobalTheory.CompanionTheory.JacquetBridge.jacquetFiniteLength k _ _ _ e _ L.ρ L.smooth (hasFiniteLength_of_isIrreducible L.irr)
  haveI : WellFoundedGT (Subrepresentation (GlobalTheory.SmGL.jac e L.ρ)) := ((hasFiniteLength_iff_wellFounded _).1 hfl).1
  have h0 : jm (dec Δ) hd L.ρ ≠ 0 := by rw [hone]; exact one_ne_zero
  have hne : (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e L.ρ)) ≠ ⊤ :=
    bot_ne_top_of_isSubquotient (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA (dec Δ)) (jhMult_ne_zero_iff.1 h0)
  obtain ⟨M, hM, -⟩ := (eq_top_or_exists_le_coatom (⊥ : Subrepresentation (GlobalTheory.SmGL.jac e L.ρ))).resolve_left hne
  let q : (GlobalTheory.SmGL.jac e L.ρ).IntertwiningMap (subQuot ⊤ M) :=
    ⟨(Submodule.mkQ _) ∘ₗ LinearMap.codRestrict (⊤ : Subrepresentation (GlobalTheory.SmGL.jac e L.ρ)).toSubmodule
      LinearMap.id (fun v => trivial), fun g => rfl⟩
  have hq : Function.Surjective q := by
    intro y
    obtain ⟨⟨v, hv⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨v, rfl⟩
  have hirr : (subQuot ⊤ M).IsIrreducible := isIrreducible_subQuot hM.covBy_top
  have hsq : IsSubquotient (subQuot ⊤ M) (GlobalTheory.SmGL.jac e L.ρ) := .of_surjective q hq
  obtain ⟨σ, ⟨ψ⟩⟩ := _root_.GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor hA (fun a => (dec Δ a).1)
    ⟨_, subQuot ⊤ M, hsq.isSmooth (isSmooth_jac e L.smooth), hirr⟩
  let y : Fin Δ.len → IrrGL (k := k) := fun a => ⟨(dec Δ a).1, σ a⟩
  have hy : ∑ a, (y a).1 = Δ.deg := hd
  let g : (GlobalTheory.SmGL.jac (stdBlocks (fun a => (y a).1) hy) L.ρ).IntertwiningMap (piTensor fun a => (y a).rep) :=
    ψ.toIntertwiningMap.comp q
  have hg : Function.Surjective g := ψ.toLinearEquiv.surjective.comp hq
  have h1 : 1 ≤ jm y hy L.ρ :=
    ENat.one_le_iff_ne_zero.2 (jhMult_ne_zero_iff.2 (IsSubquotient.of_surjective g hg))
  have hyeq : y = dec Δ := eq_dec_of_one_le_jm hA fine L.ρ hL L.smooth L.irr y hy
    (fun a => Δ.d_pos) h1
  obtain ⟨w, hw⟩ := exists_ne_zero_of_surjective (GlobalTheory.CompanionTheory.FrobJm.piTensor_rep_isIrreducible hA y) g hg
  have hfrob := GlobalTheory.T.frobenius_reciprocity_nonzero y hy L.ρ L.smooth g ⟨w, hw⟩
  have htr : ∀ (y' : Fin Δ.len → IrrGL (k := k)) (_ : y = y') (hy' : ∑ a, (y' a).1 = Δ.deg),
      (∃ g : L.ρ.IntertwiningMap (prodIrr y hy), ∃ v, g v ≠ 0) →
        ∃ g : L.ρ.IntertwiningMap (prodIrr y' hy'), ∃ v, g v ≠ 0 := by
    rintro _ rfl _ h
    exact h
  obtain ⟨g', v, hv⟩ := htr _ hyeq hd hfrob
  have hemb : Embeds L.ρ (prodIrr (dec Δ) hd) :=
    (isotypic_ne_bot_iff_embeds L.irr).1 (isotypic_ne_bot_iff.2 ⟨g', fun e' => hv (by rw [e']; rfl)⟩)
  obtain ⟨S, hS⟩ := _root_.GlobalTheory.CompanionTheory.SegSocle.exists_isSocle_prodIrr_dec hA Δ hd
  obtain ⟨a⟩ := hS.equiv_of_embeds hi ⟨f, hf⟩
  obtain ⟨b⟩ := hS.equiv_of_embeds L.irr hemb
  exact hL.of_equiv (b.trans a.symm)

end GlobalTheory.CompanionTheory.SegUniq

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalWittIsotropicToE0
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.HypWitt

theorem e0_linearIndependent (K : Type) [CommRing K] (M : ℕ) : LinearIndependent K (e0 K M) := by
  refine Fintype.linearIndependent_iff.mpr fun g hg i => ?_
  rw [Subsingleton.elim i 0]
  have h := congrFun hg 0
  simpa [e0] using h

theorem gramR_e0 {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) :
    gramR R σ (hypOne J) (e0 (R ⊗[F] E) M) = 0 := by
  ext a b
  simp [gramR, hR, hform, JR, e0, Fin.sum_univ_succ, hypOne_zero_zero]

theorem witt_e0 : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ x : Fin 1 → Fin (M + 2) → R ⊗[F] E, LinearIndependent (R ⊗[F] E) x → gramR R σ (hypOne J) x = 0 → ∃ g : HA R σ (hypOne J), actW R σ (hypOne J) g (e0 _ M) = x := by
  intro F E _ _ _ _ _ σ hσ M J hJ R _ _ _ _ _ hL x hx gx
  exact FreeTrans.transitive_free_isotropic F E σ hσ (M + 2) (hypOne J) (isHermND_hypOne σ hJ) R hL
    (e0 _ M) x (e0_linearIndependent _ M) hx (gramR_e0 R σ J) gx

end GlobalTheory.CompanionTheory.WeilSiegel.HypWitt
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormInductionOfEstimates
section
noncomputable section

open MeasureTheory Finset
open scoped InnerProductSpace ENNReal ComplexOrder

namespace GlobalTheory.CompanionTheory.RgFdNorm

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

variable {n : ℕ}

theorem cK_le_one {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (k : KG ε) : cK T k ≤ 1 := by
  have h1 := norm_inner_le_norm (𝕜 := ℂ) T.w (T.op k T.w)
  have h2 : ‖T.op k T.w‖ = ‖T.w‖ := ContinuousLinearMap.norm_map_of_mem_unitary (T.τ k).2 _
  rw [h2, T.w_norm] at h1
  simpa [cK] using h1

theorem finrank_pos_KType {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) :
    0 < Module.finrank ℂ T.V := by
  have hw : T.w ≠ 0 := fun h => by simpa [h] using T.w_norm
  have : Nontrivial T.V := ⟨T.w, 0, hw⟩
  exact Module.finrank_pos

abbrev IP (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

theorem prod_pairs (f : Fin n → Fin n → ℝ) :
    ∏ a : Fin n, ∏ b ∈ univ.filter (fun b : Fin n => a < b), f a b = ∏ p : IP n, f p.1.1 p.1.2 := by
  simp_rw [Finset.prod_filter]
  rw [← Fintype.prod_prod_type' (fun a b => if a < b then f a b else 1)]
  rw [← Finset.prod_subtype (univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp)
    (fun p => f p.1 p.2), Finset.prod_filter]

def al (lam : Fin n → ℝ) (p : IP n) : ℝ := lam p.1.1 - lam p.1.2

def be (p : IP n) : ℝ := ((p.1.2 : ℕ) : ℝ) - ((p.1.1 : ℕ) : ℝ)

theorem al_pos {lam : Fin n → ℝ} (hlam : StrictAnti lam) (p : IP n) : 0 < al lam p :=
  sub_pos.2 (hlam p.2)

theorem be_nonneg (p : IP n) : 0 ≤ be p := by
  have : ((p.1.1 : ℕ) : ℝ) ≤ ((p.1.2 : ℕ) : ℝ) := by exact_mod_cast p.2.le
  exact sub_nonneg.2 this

theorem dimVlam_eq {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    dimVlam lam = (∏ p : IP n, al lam p) / ∏ p : IP n, be p := by
  unfold dimVlam
  rw [prod_pairs (fun a b => |lam a - lam b|), prod_pairs (fun a b => ((b : ℕ) : ℝ) - ((a : ℕ) : ℝ))]
  congr 1
  exact Finset.prod_congr rfl fun p _ => abs_of_pos (al_pos hlam p)

theorem one_div_dimVlam_lamT {lam : Fin n → ℝ} (hlam : StrictAnti lam) (t : ℕ) :
    1 / dimVlam (lamT lam t) = (∏ p : IP n, be p) / ∏ p : IP n, (al lam p + t * be p) := by
  rw [dimVlam_eq (strictAnti_lamT hlam t), one_div_div]
  congr 1
  exact Finset.prod_congr rfl fun p _ => by simp only [al, be, lamT_sub]

theorem one_div_dimVlam {lam : Fin n → ℝ} (hlam : StrictAnti lam) :
    1 / dimVlam lam = (∏ p : IP n, be p) / ∏ p : IP n, al lam p := by
  rw [dimVlam_eq hlam, one_div_div]

theorem isMu_step {lam : Fin n → ℝ} {μ : Fin n → ℤ} (hμ : IsMu lam μ) (t : ℕ) :
    IsMu (lamT lam t) (μ + (t : ℤ) • Dz n) := by
  intro a
  have := hμ a
  rw [lamT_apply]
  simp only [Pi.add_apply, Pi.smul_apply, Dz, smul_eq_mul]
  push_cast
  linarith

theorem hI_nonneg (hM : PhiMul) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ)
    {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) : 0 ≤ hI T μ x p := by
  have h1 := (hM n ε μ 0 x hx p.1).1
  have h2 := (hM n ε μ 0 x hx p.2).1
  unfold hI
  positivity

theorem hI_step (hM : PhiMul) (hC : CoefPow) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : IsHCParam lam)
    (T : KType ε (lowK ε lam)) (TD : KType ε (Dvec n)) (t : ℕ) (Tt : KType ε (lowK ε (lamT lam t)))
    (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) (p : KG ε × KG ε) :
    hI Tt (μ + (t : ℤ) • Dz n) x p = hI T μ x p * hI TD (Dz n) x p ^ t := by
  unfold hI
  rw [(hM n ε μ t x hx p.1).2, (hM n ε μ t x hx p.2).2, hC n ε lam hlam T TD t Tt]
  ring

def muS (ε : Fin n → Bool) : Measure (UJ ε) := muCD ε

def PP (ε : Fin n → Bool) : Measure (UJ ε × (KG ε × KG ε)) := (muS ε).prod ((dk ε).prod (dk ε))

theorem lintegral_hs (hS : HsInt) {ε : Fin n → Bool} {Λ : Fin n → ℝ} (T : KType ε Λ) (μ : Fin n → ℤ) :
    ∫⁻ g : Formalism.REAL.UJ ε, ENNReal.ofReal (hsOp (PsiM T μ (Formalism.MainNotions.S.umat g))) ∂(muCD ε) =
      ENNReal.ofReal ((Module.finrank ℂ T.V : ℝ) ^ 2) *
        ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) := by
  obtain ⟨hm, hg⟩ := hS n ε Λ T μ
  have hm' := hm.ennreal_ofReal
  rw [PP, lintegral_prod _ hm'.aemeasurable, ← lintegral_const_mul _ hm'.lintegral_prod_right']
  exact lintegral_congr fun g => hg g

theorem posDef_pP (hP : HsPol) {ε : Fin n → Bool} (g : UJ ε) : (pP (toM g)).PosDef := by
  obtain ⟨X, hX, e⟩ := (hP n ε (toM g) g.2).1
  rw [e]
  exact exp_noncompactPart_posDef hX

theorem phiK_le_one (hP : HsPol) (hL : PhiLe) {ε : Fin n → Bool} (g : UJ ε) (k : KG ε) :
    phiK (Dz n) (pP (toM g)) k ≤ 1 := by
  obtain ⟨X, hX, e⟩ := (hP n ε (toM g) g.2).1
  rw [e]
  exact hL n ε X hX k

theorem hI_le_one (hP : HsPol) (hM : PhiMul) (hL : PhiLe) {ε : Fin n → Bool} {Λ : Fin n → ℝ}
    (T : KType ε Λ) (g : UJ ε) (p : KG ε × KG ε) : hI T (Dz n) (pP (toM g)) p ≤ 1 := by
  have hx := posDef_pP hP g
  have a1 := (hM n ε (Dz n) 0 _ hx p.1).1
  have a2 := (hM n ε (Dz n) 0 _ hx p.2).1
  have b1 := phiK_le_one hP hL g p.1
  have b2 := phiK_le_one hP hL g p.2
  have c0 : 0 ≤ cK T (p.1⁻¹ * p.2) := norm_nonneg _
  have c1 := cK_le_one T (p.1⁻¹ * p.2)
  unfold hI
  have e1 : phiK (Dz n) (pP (toM g)) p.1 * phiK (Dz n) (pP (toM g)) p.2 ≤ 1 :=
    mul_le_one₀ b1 a2.le b2
  have e2 : cK T (p.1⁻¹ * p.2) ^ 2 ≤ 1 := pow_le_one₀ c0 c1
  exact mul_le_one₀ e1 (by positivity) e2

theorem mass_of_normAt (hS : HsInt) {ε : Fin n → Bool} {lam : Fin n → ℝ} (hN : NormAt ε lam)
    (T : KType ε (lowK ε lam)) (μ : Fin n → ℤ) (hμ : IsMu lam μ) :
    ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) = ENNReal.ofReal (1 / dimVlam lam) := by
  have h := hN T μ hμ
  rw [lintegral_hs hS] at h
  have hd : (0 : ℝ) < (Module.finrank ℂ T.V : ℝ) ^ 2 := by
    have := finrank_pos_KType T
    positivity
  have e : (Module.finrank ℂ T.V : ℝ) ^ 2 / dimVlam lam =
      (Module.finrank ℂ T.V : ℝ) ^ 2 * (1 / dimVlam lam) := by ring
  rw [e, ENNReal.ofReal_mul hd.le] at h
  exact (ENNReal.mul_right_inj (ENNReal.ofReal_pos.2 hd).ne' ENNReal.ofReal_ne_top).1 h

theorem gap_of_le {ε : Fin n → Bool} {lam : Fin n → ℝ} (hlam : StrictAnti lam) {h0 : ℝ} {t : ℕ}
    (ht : ⌈h0⌉₊ ≤ t) : GapAtLeast ε (lamT lam t) h0 := by
  have g0 : GapAtLeast ε lam 0 := fun a b _ => abs_nonneg _
  have g1 := gap_lamT hlam g0 t
  intro a b hab
  have h1 := g1 a b hab
  have h2 : h0 ≤ (t : ℝ) := (Nat.le_ceil h0).trans (by exact_mod_cast ht)
  linarith

theorem ae_eq_indicator (hP : HsPol) (hM : PhiMul) (hK : KNull) {ε : Fin n → Bool} {lam : Fin n → ℝ}
    (hlam : IsHCParam lam) (T : KType ε (lowK ε lam)) (TD : KType ε (Dvec n)) (μ : Fin n → ℤ) :
    (fun z : UJ ε × (KG ε × KG ε) => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2)) =ᵐ[PP ε]
      ({z : UJ ε × (KG ε × KG ε) | 0 < hI TD (Dz n) (pP (toM z.1)) z.2}).indicator
        (fun z => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2)) := by
  have h1 := hK n ε lam hlam T TD
  have h2 : ∀ᵐ p ∂((dk ε).prod (dk ε)), cK TD (p.1⁻¹ * p.2) = 0 → cK T (p.1⁻¹ * p.2) = 0 :=
    (measurePreserving_prod_inv_mul (dk ε) (dk ε)).quasiMeasurePreserving.ae
      (Measure.quasiMeasurePreserving_snd.ae h1)
  have h3 : ∀ᵐ z ∂(PP ε), cK TD (z.2.1⁻¹ * z.2.2) = 0 → cK T (z.2.1⁻¹ * z.2.2) = 0 :=
    Measure.quasiMeasurePreserving_snd.ae h2
  filter_upwards [h3] with z hz
  by_cases hz0 : 0 < hI TD (Dz n) (pP (toM z.1)) z.2
  · rw [Set.indicator_of_mem (by exact hz0)]
  · rw [Set.indicator_of_notMem (by exact hz0)]
    have hx := posDef_pP hP z.1
    have a1 := (hM n ε (Dz n) 0 _ hx z.2.1).1
    have a2 := (hM n ε (Dz n) 0 _ hx z.2.2).1
    have hc : cK TD (z.2.1⁻¹ * z.2.2) = 0 := by
      by_contra hne
      have : 0 < cK TD (z.2.1⁻¹ * z.2.2) := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hne)
      exact hz0 (by unfold hI; positivity)
    have hT := hz hc
    simp [hI, hT]

theorem norm_induction_of_estimates : MomW → CoefPow → KNull → HsPol → PhiMul → PhiLe → PhiCont → HsInt → GapNorm → NormInd := by
  intro hMom hC hK hP hM hL _ hS hG n ε hp hq lam hlam T μ hμ
  obtain ⟨h0, hg⟩ := hG n ε hp hq
  obtain ⟨TD⟩ := HW.kType_exists_of_dom ε (Dvec n) (fun a => ⟨Dz n a, by simp [Dvec, Dz]⟩)
    (fun a b hab _ => dvec_antitone hab.le)
  have hUm : Measurable fun z : UJ ε × (KG ε × KG ε) => hI TD (Dz n) (pP (toM z.1)) z.2 :=
    (hS n ε _ TD (Dz n)).1
  have hhm : Measurable fun z : UJ ε × (KG ε × KG ε) => ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) :=
    (hS n ε _ T μ).1.ennreal_ofReal
  have hmom : ∀ t : ℕ, ⌈h0⌉₊ ≤ t →
      ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) *
          ENNReal.ofReal (hI TD (Dz n) (pP (toM z.1)) z.2 ^ t) ∂(PP ε) =
        ENNReal.ofReal ((∏ p : IP n, be p) / ∏ p : IP n, (al lam p + t * be p)) := by
    intro t ht
    obtain ⟨Tt⟩ := HW.kType_exists ε (lamT lam t) (isHCParam_lamT hlam t)
    rw [← one_div_dimVlam_lamT hlam.1 t,
      ← mass_of_normAt hS (hg _ (isHCParam_lamT hlam t) (gap_of_le hlam.1 ht)) Tt _ (isMu_step hμ t)]
    refine lintegral_congr fun z => ?_
    rw [hI_step hM hC hlam T TD t Tt μ (posDef_pP hP z.1),
      ENNReal.ofReal_mul (hI_nonneg hM T μ (posDef_pP hP z.1) z.2)]
  have key := hMom _ (PP ε) _ _ (IP n) (al lam) be (∏ p : IP n, be p) ⌈h0⌉₊ hhm hUm
    (fun z => ⟨hI_nonneg hM TD _ (posDef_pP hP z.1) z.2, hI_le_one hP hM hL TD z.1 z.2⟩)
    (al_pos hlam.1) be_nonneg (Finset.prod_nonneg fun p _ => be_nonneg p) hmom
  rw [← one_div_dimVlam hlam.1] at key
  have hmass : ∫⁻ z, ENNReal.ofReal (hI T μ (pP (toM z.1)) z.2) ∂(PP ε) =
      ENNReal.ofReal (1 / dimVlam lam) := by
    rw [lintegral_congr_ae (ae_eq_indicator hP hM hK hlam T TD μ),
      lintegral_indicator (measurableSet_lt measurable_const hUm)]
    exact key
  rw [lintegral_hs hS, hmass, ← ENNReal.ofReal_mul (sq_nonneg _), mul_one_div]

end GlobalTheory.CompanionTheory.RgFdNorm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ReverseOrderedProductHasSocleStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.reverse_ordered_product_has_socle : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], GlobalTheory.Published.IrreducibleAdmissibleGL → LSegJacquet k → LUnlinkedIrr k → LUnlinkedComm k → ∀ {h N : ℕ} (Γ : Fin h → Segment k) (y : Fin h → IrrGL (k := k)) (hd : ∑ a, (y a).1 = N), IsRevOrdered Γ → (∀ i, IsLSeg (Γ i) (y i).rep) → ∃ τ : IrrRep (GL (Fin N) k), IsSocle τ.ρ (prodIrr y hd) := by
  first | exact @GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | exact GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered | (intros; apply GlobalTheory.CompanionTheory.SocleRev.exists_isSocle_prodIrr_of_isRevOrdered <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaIntegralLeFundamentalSet
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.SiegelFormula
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilConv

theorem absThetaInt_le_of_meets_orbits (D : D7) (V : HSp D) (ν : Measure (GA D V)) (hν : ν.IsHaarMeasure) {n : ℕ}
    (φ : Mx D V.rank n → ℂ) (hφ : Continuous φ) (S : Set (GA D V)) (hS : MeasurableSet S)
    (hcov : ∀ g, ∃ γ ∈ GQ V, γ * g ∈ S) : absThetaInt V ν φ ≤ ∫⁻ g in S, absTheta V φ g ∂ν := by
  have hinv := leftInv_absTheta V φ
  have hfd : IsFundamentalDomain (GQ V) (stdDom (GQ V)) ν := isFundamentalDomain_stdDom _ ν
  have e : absThetaInt V ν φ = ∫⁻ g in stdDom (GQ V), absTheta V φ g ∂ν := by
    unfold absThetaInt
    show ∫⁻ q, descend (GQ V) (absTheta V φ) q ∂GlobalTheory.AutomorphicL2Unitary.quotMeasure (GQ V) ν = _
    rw [GlobalTheory.AutomorphicL2Unitary.lintegral_quotMeasure hfd]
    exact lintegral_congr fun g => congrFun hinv.lift_descend g
  rw [e]
  exact GlobalTheory.lintegral_fundamentalDomain_le_of_meets_orbits (GQ V) ν hfd hS hcov (GlobalTheory.AbsThetaSemi.measurable_absTheta V hφ) hinv

end GlobalTheory.CompanionTheory.WeilConv

end
end

