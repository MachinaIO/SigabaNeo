# Pouly–Shen cost evidence for Kyber

> Status: incomplete. No sampler-inclusive bit-operation count was obtained; the revised (2026-05-28) paper could not be retrieved, so only the authors' historical 2024 totals are compared. Not audited as a result.

The authors describe the Kyber costs as rough estimates using an MCMC discrete Gaussian sampler. The archive dates their correction to May 28, 2026. Retrieval of the revised PDF returned HTTP 403, and the scratchpad file with a PDF suffix contained HTML. The revised table, its individual components, and any changes to Theorem 6 could not be verified from that version. The repository literature survey labels its corrected totals as inferred. [Revision history and authors’ abstract](https://eprint.iacr.org/2023/1508)

## What the probability bound measures

According to the repository’s reading of Theorem 6, the public matrix, secret and error are fixed. Conditional on the geometric separation and rank hypotheses, independent draws from the specified lattice Gaussian give a failure bound of the form $q^m 2^{-\Omega(N\delta^2)}$ for recovery of the guessed block. Here $m$ counts equations, $N$ counts dual draws and $\delta$ measures score separation. The stated time with the list supplied is $\mathrm{poly}(m,n)(N+q^{n_{\rm guess}})$. Neither expression specifies a numerical bit-operation count. The repository’s Lean fresh-sample theorem also draws fresh right-hand sides, which changes the probability space. [Theorem 6 reading](provable_dual.md) and [finite sampler analysis](dual_sampler.md)

A sampler analysis needs both an accuracy budget and a cost per draw. For example, if independent approximate draws are each within total variation distance $\epsilon$ of their targets, coupling bounds the additional failure probability by $1-(1-\epsilon)^N\le N\epsilon$. A marginal guarantee alone leaves dependence between successive MCMC outputs unaccounted for. The geometric series assumption models the reduced basis profile. A core-SVP estimate assigns a cost to reduction. Neither establishes the numerical mixing time or gate count for the basis actually obtained. A certified comparison would require bounds on preprocessing, joint sampling error, sampling time, and finite-precision score evaluation in a common operation model. The revised Gaussian width relative to smoothing, sample counts, block sizes, and component timings remain unverified.

## Historical numerical comparison

The PS column transcribes the no-modulus-switching estimate on slide 9. The original paper’s Table 1 discussion explicitly omits polynomial factors. The estimator columns use the classical dual and dual-hybrid values recorded for the module-LWE instance without ciphertext rounding. Subtraction compares reported base-two logarithms at their displayed precision. The differences have no interpretation as certified security margins. [Authors’ slides](https://www.pouly.fr/data/slides/eurocrypt2024.pdf) and [repository estimator table](../LWE_ESTIMATOR.md#kyber)

| Kyber | PS (2024) | dual | dual hybrid | PS − dual | PS − hybrid |
| --- | ---: | ---: | ---: | ---: | ---: |
| 512 | 185 | 149.88 | 139.66 | 35.12 | 45.34 |
| 768 | 273 | 214.29 | 196.37 | 58.71 | 76.63 |
| 1024 | 376 | 288.53 | 262.34 | 87.47 | 113.66 |
