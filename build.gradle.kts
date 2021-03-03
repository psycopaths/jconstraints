/*
 * Copyright 2017-2021 The jConstraints-cvc4 Authors
 * SPDX-License-Identifier: Apache-2.0
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 * http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

import org.gradle.api.tasks.testing.logging.TestLogEvent.FAILED
import org.gradle.api.tasks.testing.logging.TestLogEvent.PASSED
import org.gradle.api.tasks.testing.logging.TestLogEvent.SKIPPED
import org.gradle.api.tasks.testing.logging.TestLogEvent.STANDARD_ERROR
import java.time.LocalDate.now

plugins {
    `java-library`
    `maven-publish`
    id("com.github.sherter.google-java-format") version "0.9"
    id("com.github.johnrengelman.shadow") version "5.2.0"
    id("org.cadixdev.licenser") version "0.5.0"
}

repositories {
    maven { url = uri("https://jitpack.io") }
    mavenLocal()
    mavenCentral()
}


group = "tools.aqua"
version = "0.9.6-SNAPSHOT"
description = "JConstraints-cvc4"

dependencies {

    //Use jitpack.io until a better solution is in place for jConstraints
    implementation("com.github.tudo-aqua:jconstraints:b057fe7")
    implementation("io.github.tudo-aqua:cvc4-turnkey-permissive:1.8")
    implementation("org.apache.commons:commons-math3:3.6.1")

    testImplementation("org.testng:testng:7.0.0")
}

val test by tasks.getting(Test::class) {
    // Use TestNG for unit tests
    useTestNG()
    testLogging {
        events(FAILED, STANDARD_ERROR, SKIPPED, PASSED)
    }
}

tasks.shadowJar {
    exclude("tools.aqua:jconstraints:.*")

}

license {
    header = project.file("contrib/license-header.txt")
    ext["year"] = now().year

    exclude("**/*.smt2", "**/*.txt")

    tasks {
        create("buildFiles") {
            files = project.files("build.gradle.kts", "settings.gradle.kts")
        }
    }
}

publishing {
    publications {
        create<MavenPublication>("mavenJava") {
            artifactId = "jconstraints-cvc4"
            from(components["java"])
            pom {
                name.set("jConstraints-cvc4")
                description.set("JConstraints-cvc4 is the CVC4 API plug-in for JConstraints.")
                url.set("https://github.com/tudo-aqua/jconstraints-cvc4")
                licenses {
                    license {
                        name.set("Apache-2.0")
                        url.set("https://www.apache.org/licenses/LICENSE-2.0.txt")
                    }
                }
                developers {
                    developer {
                        id.set("mmuesly")
                        name.set("Malte Mues")
                        email.set("mail.mues@gmail.com")
                    }
                }
                scm {
                    connection.set("https://github.com/tudo-aqua/jconstraints-cvc4")
                    url.set("https://github.com/tudo-aqua/jconstraints-cvc4")
                }
            }
        }
        create<MavenPublication>("publishMaven") {
            artifact(tasks["shadowJar"]) {
                classifier = null
            }
            artifactId = "jconstraints-cvc4-all"

        }
    }
}
