# Benchmarking Tests


We present a collection of known, used, examples from MPST/Actor community to highlight our language's efficacy.


## Stay Safe under Panic: Affine Rust Programming with Multiparty Session Types

| Example (Endpoint)            | Check./Comp./Rel./Exec. Time   | LoC Impl. | Gen Types/All | MP | Rec |
|-------------------------------|--------------------------------|-----------|---------------|----|-----|
| Three buyers [25]             | 26.7s / 37.1s / 81.3s / 568 µs | 143       | 37 / 180      | ✓  | ✓   |
| Calculator [19]               | 26.5s / 36.9s / 81.3s / 467 µs | 136       | 32 / 168      | ✗  | ✗   |
| Travel agency [21]            | 26.5s / 37.6s / 84.8s / 8 ms   | 200       | 47 / 247      | ✗  | ✓   |
| Simple voting [19]            | 26.3s / 36.7s / 82.4s / 396 µs | 207       | 61 / 268      | ✗  | ✗   |
| Online wallet [39]            | 26.4s / 37.8s / 84.4s / 759 µs | 231       | 76 / 307      | ✗  | ✓   |
| Fibonacci [19]                | 26.6s / 36.7s / 80.9s / 9 ms   | 141       | 23 / 164      | ✗  | ✓   |
| Video Streaming service (§ 2) | 26.3s / 37.4s / 83.0s / 11 ms  | 104       | 39 / 143      | ✓  | ✓   |
| oAuth2 [39]                   | 26.4s / 37.5s / 83.2s / 12 ms  | 215       | 61 / 276      | ✓  | ✓   |
| Distributed logging ([30])    | 26.5s / 36.8s / 82.6s / 5 ms   | 252       | 59 / 311      | ✗  | ✓   |
| Circuit breaker ([30])        | 26.5s / 38.5s / 87.0s / 18 ms  | 375       | 142 / 517     | ✓  | ✓   |
| SMTP [12]                     | 26.4s / 41.1s / 97.3s / 5 ms   | 571       | 143 / 714     | ✗  | ✓   |
